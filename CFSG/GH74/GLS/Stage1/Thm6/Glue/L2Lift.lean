module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Four

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

theorem exists_three_cycle_action {Y : Type*} [Group Y] {W : Subgroup Y} (hW : Dihedral.IsEA W)
    (hc : Nat.card W = 4)
    (hY : Nonempty (Y ≃* alternatingGroup (Fin 4)) ∨ Nonempty (Y ≃* Equiv.Perm (Fin 4))) :
    ∃ m : Y, m ^ 3 = 1 ∧ ∃ w ∈ W, m * w * m⁻¹ ≠ w := by
  obtain ⟨a, ha, -, -, ha1, -, -⟩ := Dihedral.exists_two_ne_one W hc
  have hcA : ∃ c : alternatingGroup (Fin 4), c ^ 3 = 1 ∧ ∀ w : alternatingGroup (Fin 4),
      w * w = 1 → w ≠ 1 → c * w * c⁻¹ ≠ w := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, by decide, by decide⟩
  have hcS : ∃ c : Equiv.Perm (Fin 4), c ^ 3 = 1 ∧ ∀ w : Equiv.Perm (Fin 4),
      w * w = 1 → w ≠ 1 → c * w * c⁻¹ ≠ w := by
    refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide⟩
  rcases hY with ⟨⟨e₂⟩⟩ | ⟨⟨e₂⟩⟩
  · obtain ⟨c, hc3, hcw⟩ := hcA
    refine ⟨e₂.symm c, by rw [← map_pow, hc3, map_one], a, ha, fun h => ?_⟩
    apply hcw (e₂ a) (by rw [← map_mul, (hW a ha).1, map_one])
      (fun h1 => ha1 (e₂.injective (by rw [h1, map_one])))
    have := congrArg e₂ h
    simpa using this
  · obtain ⟨c, hc3, hcw⟩ := hcS
    refine ⟨e₂.symm c, by rw [← map_pow, hc3, map_one], a, ha, fun h => ?_⟩
    apply hcw (e₂ a) (by rw [← map_mul, (hW a ha).1, map_one])
      (fun h1 => ha1 (e₂.injective (by rw [h1, map_one])))
    have := congrArg e₂ h
    simpa using this

variable {G : Type} [Group G] [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

omit [Finite G] in
theorem mem_map_mk_iff {V : Subgroup G} {y : CentralizerBar x} :
    y ∈ (V.subgroupOf (Cx x)).map (QuotientGroup.mk' (Ox x)) ↔ ∃ g ∈ V, ∃ hg : g ∈ Cx x,
      (QuotientGroup.mk ⟨g, hg⟩ : CentralizerBar x) = y := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.1, hg', g'.2, rfl⟩
  · rintro ⟨g, hg, hgC, rfl⟩
    exact ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩

theorem isEA_subgroupOf' {X : Type*} [Group X] {H V : Subgroup X} (hV : Dihedral.IsEA V) :
    Dihedral.IsEA (V.subgroupOf H) := by
  intro a ha
  have ha' : (a : X) ∈ V := ha
  refine ⟨Subtype.ext ((hV _ ha').1), fun b hb => Subtype.ext ((hV _ ha').2 _ hb)⟩

theorem mem_timgP_conj_iff (h : SitFacts x Kb e N T) {V : Subgroup G} (hVP : V ≤ Pg x Kb T)
    (y : ↥Kb) : MulAut.conj y ∈ timgP h V ↔ ∃ g ∈ V, pr x g = (y : CentralizerBar x) := by
  have hconj := IVK.conj_injective_of_L2 e
  constructor
  · intro hy
    obtain ⟨g, hg, hgy⟩ := (mem_timgP h hVP).1 hy
    refine ⟨g, hg, ?_⟩
    rw [phig_eq_conj x Kb (hVP hg).2] at hgy
    have := hconj hgy
    exact congrArg Subtype.val this
  · rintro ⟨g, hg, hgy⟩
    refine (mem_timgP h hVP).2 ⟨g, hg, ?_⟩
    rw [phig_eq_conj x Kb (hVP hg).2]
    congr 1
    exact Subtype.ext hgy

theorem ip_f3 (h : SitFacts x Kb e N T) (h13fc : IVK.IVK_1_3f_c) : IP_f3 x (Pg x Kb T) := by
  intro V hVP hV
  have hVC : ∀ g ∈ V, g ∈ Cx x := fun g hg => ((mem_Kg x Kb).1 (hVP hg).2).1
  have hconj := IVK.conj_injective_of_L2 e
  have hV4 : IVK.IsFourSubgroup (timgP h V) :=
    isFourSubgroup_of_isEA (isEA_timgP h hVP hV.1) (by rw [card_timgP h hVP]; exact hV.2)
  have hVinn : timgP h V ≤ IVK.innAut ↥Kb := fun a ha => (NP_mem_iff.1 (timgP_le h V ha)).2
  have h3 := h13fc F h.hF ↥Kb e (timgP h V) hVinn hV4
  let M : Subgroup (MulAut ↥Kb) :=
    Subgroup.normalizer ((timgP h V : Subgroup (MulAut ↥Kb)) : Set (MulAut ↥Kb)) ⊓ IVK.innAut ↥Kb
  have hVM : timgP h V ≤ M := fun a ha => ⟨Subgroup.le_normalizer ha, hVinn ha⟩
  have hEA := isEA_timgP h hVP hV.1
  have hcard : Nat.card (timgP h V) = 4 := by rw [card_timgP h hVP]; exact hV.2
  obtain ⟨mY, hmY3, w, hw, hmw⟩ := exists_three_cycle_action
    (W := (timgP h V).subgroupOf M) (isEA_subgroupOf' hEA) (by rw [card_subgroupOf hVM]; exact hcard)
    h3
  have hmN : (mY : MulAut ↥Kb) ∈ Subgroup.normalizer ((timgP h V : Subgroup (MulAut ↥Kb)) :
      Set (MulAut ↥Kb)) := mY.2.1
  have hm3 : (mY : MulAut ↥Kb) ^ 3 = 1 := by simpa using congrArg Subtype.val hmY3
  obtain ⟨k, hk⟩ := mY.2.2
  have hwV : (w : MulAut ↥Kb) ∈ timgP h V := Subgroup.mem_subgroupOf.1 hw
  have hmw' : (mY : MulAut ↥Kb) * (w : MulAut ↥Kb) * (mY : MulAut ↥Kb)⁻¹ ≠ (w : MulAut ↥Kb) :=
    fun hh => hmw (Subtype.ext (by simpa using hh))
  have hk3 : k ^ 3 = 1 := by
    apply hconj
    rw [map_pow, hk, hm3, map_one]
  set fbar : CentralizerBar x := (k : CentralizerBar x) with hfbar
  have hfbar3 : fbar ^ 3 = 1 := by
    have := congrArg (fun z : ↥Kb => (z : CentralizerBar x)) hk3
    simpa using this
  have hVT : V ≤ T := fun g hg => (hVP hg).1
  have hE2 : IsPGroup 2 ↥(V.subgroupOf (Cx x)) :=
    ((h.sylow.2.1.to_le hVT).of_equiv (Subgroup.subgroupOfEquivOfLe (fun g hg => hVC g hg)).symm)
  have hEab : ∀ a ∈ V.subgroupOf (Cx x), ∀ b ∈ V.subgroupOf (Cx x), a * b = b * a :=
    fun a ha b hb => Subtype.ext ((hV.1 _ ha).2 _ hb)
  have hconjk : ∀ y : ↥Kb, MulAut.conj k * MulAut.conj y * (MulAut.conj k)⁻¹ =
      MulAut.conj (k * y * k⁻¹) := fun y => by simp [map_mul, map_inv]
  have hmem_iff : ∀ y : ↥Kb, MulAut.conj y ∈ timgP h V ↔
      MulAut.conj (k * y * k⁻¹) ∈ timgP h V := by
    intro y
    rw [← hconjk, hk]
    exact Subgroup.mem_normalizer_iff.1 hmN _
  have hf : ∀ y : CentralizerBar x, y ∈ (V.subgroupOf (Cx x)).map (QuotientGroup.mk' (Ox x)) ↔
      fbar * y * fbar⁻¹ ∈ (V.subgroupOf (Cx x)).map (QuotientGroup.mk' (Ox x)) := by
    intro y
    rw [mem_map_mk_iff, mem_map_mk_iff]
    have hprm : ∀ g : G, ∀ hg : g ∈ Cx x, (QuotientGroup.mk ⟨g, hg⟩ : CentralizerBar x) = pr x g :=
      fun g hg => (pr_of_mem x hg).symm
    constructor
    · rintro ⟨g, hg, hgC, hgy⟩
      have hyK : y ∈ Kb := by rw [← hgy, hprm]; exact ((mem_Kg x Kb).1 (hVP hg).2).2
      have h1 : MulAut.conj (⟨y, hyK⟩ : ↥Kb) ∈ timgP h V :=
        (mem_timgP_conj_iff h hVP _).2 ⟨g, hg, by
          show pr x g = y
          rw [← hprm g hgC]; exact hgy⟩
      obtain ⟨g', hg', hg'y⟩ := (mem_timgP_conj_iff h hVP _).1 ((hmem_iff _).1 h1)
      exact ⟨g', hg', hVC g' hg', by rw [hprm]; simpa [hfbar] using hg'y⟩
    · rintro ⟨g', hg', hg'C, hg'y⟩
      have hy'K : fbar * y * fbar⁻¹ ∈ Kb := by
        rw [← hg'y, hprm]; exact ((mem_Kg x Kb).1 (hVP hg').2).2
      have hyK : y ∈ Kb := by
        have := Kb.mul_mem (Kb.mul_mem (Kb.inv_mem k.2) hy'K) k.2
        simpa [hfbar, mul_assoc] using this
      have h1 : MulAut.conj (k * (⟨y, hyK⟩ : ↥Kb) * k⁻¹) ∈ timgP h V :=
        (mem_timgP_conj_iff h hVP _).2 ⟨g', hg', by rw [← hprm g' hg'C, hg'y]; simp [hfbar]⟩
      obtain ⟨g, hg, hgy⟩ := (mem_timgP_conj_iff h hVP _).1 ((hmem_iff _).2 h1)
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
    have hE' : n ^ 3 * ee * (n ^ 3)⁻¹ ∈ V.subgroupOf (Cx x) := (pow_mem_normalizer_aux hn1 3 ee).1 hee
    have hd : (n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹ ∈ V.subgroupOf (Cx x) :=
      mul_mem hE' (inv_mem hee)
    have hmk : (QuotientGroup.mk ((n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹) : CentralizerBar x) = 1 := by
      rw [QuotientGroup.mk_mul, hpow 3 ee hee, hfbar3, QuotientGroup.mk_inv]
      simp
    have hd1 : (n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹ = 1 := by
      apply Subtype.ext
      apply eq_one_of_pr_eq_one x h.sylow (hVT hd) (((n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹ : ↥(Cx x))).2
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
  · obtain ⟨g₀, hg₀, hg₀w⟩ := (mem_timgP h hVP).1 hwV
    refine ⟨g₀, hg₀, fun hcon => hmw' ?_⟩
    have hee : (⟨g₀, hVC g₀ hg₀⟩ : ↥(Cx x)) ∈ V.subgroupOf (Cx x) := Subgroup.mem_subgroupOf.2 hg₀
    have h1 : m' * ⟨g₀, hVC g₀ hg₀⟩ * m'⁻¹ = ⟨g₀, hVC g₀ hg₀⟩ := Subtype.ext hcon
    rw [hm'2 _ hee] at h1
    have h2 := hn2 _ hee
    rw [h1] at h2
    have h3 : fbar * pr x g₀ * fbar⁻¹ = pr x g₀ := by
      rw [pr_of_mem x (hVC g₀ hg₀)]; exact h2.symm
    have h4 : k * (⟨pr x g₀, ((mem_Kg x Kb).1 (hVP hg₀).2).2⟩ : ↥Kb) * k⁻¹ =
        ⟨pr x g₀, ((mem_Kg x Kb).1 (hVP hg₀).2).2⟩ := Subtype.ext (by simpa [hfbar] using h3)
    rw [← hg₀w, phig_eq_conj x Kb (hVP hg₀).2, ← hk, hconjk, h4]

end CFSG.GH74.GLS.Stage1.Thm6.Glue
