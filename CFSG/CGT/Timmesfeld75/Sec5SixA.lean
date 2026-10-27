module

public import CFSG.CGT.Timmesfeld75.Sec5SixKer
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Four

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

section Six

variable [Finite G]

theorem commute_conj_secA_of_exists (hP : MaxPair T T₁) (hS : Sec3Global T) {g h : G} {y : G}
    (hy : y ∈ conjSubgroup g (secA T T₁)) (hy1 : y ≠ 1)
    (hyc : ∀ a ∈ conjSubgroup h (secA T T₁), a * y = y * a) :
    ∀ a ∈ conjSubgroup h (secA T T₁), ∀ x ∈ conjSubgroup g (secA T T₁), a * x = x * a := by
  intro a ha x hx
  by_cases ha1 : a = 1
  · rw [ha1]
    simp
  have haT : a ∈ conjSubgroup h T := conjSubgroup_mono secA_le_left ha
  have haD : a ∈ classD T := mem_classD_of_mem_conjSubgroup haT ha1
  have hyT : y ∈ conjSubgroup g T := conjSubgroup_mono secA_le_left hy
  have haN : a ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) :=
    (hP.wc.conj g).centralizer_le_normalizer hyT hy1
      (Subgroup.mem_centralizer_singleton_iff.2 (hyc a ha))
  exact (conjSubgroup_secA_comm_of_mem_normalizer hP hS haD haN x hx).symm

theorem commute_conj_secA_conj_secA_of_card_lt (h1 : Sec4NoA) (h3 : Sec4Nine)
    (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    (hcard : Nat.card T < Nat.card (secA T T₁) * Nat.card (normIn T T₁)) {g h : G}
    (hg : IsUIdx T T₁ g) (hh : IsUIdx T T₁ h) :
    ∀ a ∈ conjSubgroup h (secA T T₁), ∀ x ∈ conjSubgroup g (secA T T₁), a * x = x * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀, x₀', hx₀', hne₀⟩ := hcon
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hy' : StepHyp T (conjSubgroup h T) := hh.stepHyp hy hS
  have hP' := hy'.pair
  have hA4' : secA T (conjSubgroup h T) ≠ normIn T (conjSubgroup h T) :=
    secA_ne_normIn hTO hBW hy.nonab hP' hS
  have hAeq : secA T (conjSubgroup h T) = secA T T₁ := secA_eq_of_isUIdx hP hS hh
  have hRe : secR₁ T (conjSubgroup h T) = secR₁ T T₁ := secR₁_eq_of_isUIdx hP hS hh
  have hClaim : ∀ y ∈ conjSubgroup g (secA T T₁), y ≠ 1 →
      ∃ a ∈ conjSubgroup h (secA T T₁), a * y ≠ y * a := by
    intro y hyg hy1
    by_contra hcon'
    push Not at hcon'
    exact hne₀ (commute_conj_secA_of_exists hP hS hyg hy1 hcon' a₀ ha₀ x₀' hx₀')
  have hsec3' : Sec3 T (conjSubgroup h T) := hh.sec3 hP hS
  have hcfg' := hsec3'.cfg
  have hMX : cfgM T (conjSubgroup h T) ≤ T ⊔ conjSubgroup h T := cfgM_le_sup _ _
  have hMn : ∀ x ∈ T ⊔ conjSubgroup h T, ∀ m ∈ cfgM T (conjSubgroup h T),
      x * m * x⁻¹ ∈ cfgM T (conjSubgroup h T) := fun x hx m hm => hcfg'.conj_mem_cfgM hx hm
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup G,
      Z = trivActing (T ⊔ conjSubgroup h T) (cfgM T (conjSubgroup h T)) hMX := ⟨_, rfl⟩
  have hTZ : T ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZ]
    exact le_sup_left.trans (X_le_normalizer_trivActing hMX hMn)
  have hA₁R : conjSubgroup h (secA T (conjSubgroup h T)) ≤ secR₁ T (conjSubgroup h T) := by
    unfold secR₁
    exact le_iSup₂ (f := fun (k : G) (_ : IsUIdx T (conjSubgroup h T) k) =>
      conjSubgroup k (secA T (conjSubgroup h T))) h ((isUIdx_conj_iff hP hS hh).2 hh)
  have hex : ∀ y ∈ conjSubgroup g (secA T T₁), ∃ t ∈ T, y * t ∈ Z := by
    intro y hyg
    by_cases hy1 : y = 1
    · refine ⟨1, T.one_mem, ?_⟩
      rw [hy1, mul_one]
      exact Z.one_mem
    obtain ⟨a, haA, hane⟩ := hClaim y hyg hy1
    have hyN : y ∈ Subgroup.normalizer (T : Set G) := hg.conj_secA_le_normalizer hP hS hyg
    have hyT : y ∈ conjSubgroup g T := conjSubgroup_mono secA_le_left hyg
    have hyy : y * y = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup hP.wc.1 g) hyT
    have hyD : y ∈ classD T := mem_classD_of_mem_conjSubgroup hyT hy1
    have hyR : y ∈ secR₁ T (conjSubgroup h T) := by
      rw [hRe]
      unfold secR₁
      exact (le_iSup₂ (f := fun (k : G) (_ : IsUIdx T T₁ k) => conjSubgroup k (secA T T₁)) g hg)
        hyg
    have hE2 := conj_normIn_le_of_mem_secR₁ h1 h3 hy' hS hI hA4' hyR
    have hE4 : ∀ a ∈ conjSubgroup h (secA T (conjSubgroup h T)), ⁅a, y⁆ ∈ T := fun a ha =>
      commutator_secR₁_mem h1 h3 hy' hS hI hA4' a (hA₁R ha) y hyR
    have hne : ∃ a ∈ conjSubgroup h (secA T (conjSubgroup h T)), ⁅a, y⁆ ≠ 1 :=
      ⟨a, by rw [hAeq]; exact haA, fun h' => hane (commutatorElement_eq_one_iff_mul_comm.1 h')⟩
    obtain ⟨t, htT, hxt⟩ := engine hy' hS hI hA4' (x₀ := h) rfl hyN hyy hyD hE2 hE4 hne
    refine ⟨t, htT, ?_⟩
    have hu1 : ∀ z ∈ T ⊔ conjSubgroup h T,
        (y * t) * z * (y * t)⁻¹ ∈ T ⊔ conjSubgroup h T := by
      intro z hz
      have hm := hMX (hxt z hz)
      have h4 := (T ⊔ conjSubgroup h T).mul_mem hz hm
      rwa [mul_inv_cancel_left] at h4
    have hconj : conjSubgroup (y * t) (T ⊔ conjSubgroup h T) = T ⊔ conjSubgroup h T := by
      refine conjSubgroup_eq_of_le fun w hw => ?_
      have hz := mem_conjSubgroup.1 hw
      have e : w = (y * t) * ((y * t)⁻¹ * w * (y * t)) * (y * t)⁻¹ := by group
      rw [e]
      exact hu1 _ hz
    rw [hZ]
    refine ⟨fun z hz => ⟨hu1 z hz, ?_⟩, hxt⟩
    have hz' : z ∈ conjSubgroup (y * t) (T ⊔ conjSubgroup h T) := by rw [hconj]; exact hz
    exact mem_conjSubgroup.1 hz'
  have hcard' : Nat.card T < Nat.card (conjSubgroup g (secA T T₁)) * Nat.card ↥(T ⊓ Z) := by
    rw [card_conjSubgroup]
    have hle : normIn T (conjSubgroup h T) ≤ T ⊓ Z := by
      rw [← hcfg'.inf_cfgM, hZ]
      exact inf_le_inf_left T (le_trivActing hMX hMn)
    have h2 : Nat.card (normIn T (conjSubgroup h T)) ≤ Nat.card ↥(T ⊓ Z) :=
      Subgroup.card_le_of_le hle
    have h5 : Nat.card (normIn T (conjSubgroup h T)) = Nat.card (normIn T T₁) :=
      hh.card_normIn hP hS
    calc Nat.card T < Nat.card (secA T T₁) * Nat.card (normIn T T₁) := hcard
      _ ≤ Nat.card (secA T T₁) * Nat.card ↥(T ⊓ Z) := Nat.mul_le_mul_left _ (h5 ▸ h2)
  obtain ⟨y, hyg, hy1, hyZ⟩ := exists_ne_one_mem_of_card_lt hTZ hex hcard'
  have hyZ' := hyZ
  rw [hZ] at hyZ'
  have hnorm : conjSubgroup h T ≤ Subgroup.normalizer
      ((cfgM T (conjSubgroup h T) : Subgroup G) : Set G) := fun z hz =>
    hcfg'.le_normalizer_cfgM (Subgroup.mem_sup_right hz)
  have hM2 : IsPGroup 2 ↥(cfgM T (conjSubgroup h T)) :=
    isPGroup_two_of_isElemAbelian hcfg'.isElemAbelian_cfgM
  have hT2 : IsPGroup 2 ↥(conjSubgroup h T) := isPGroup_two_of_isElemAbelian hcfg'.wc₁.1
  have hS2 : IsPGroup 2 ↥(cfgM T (conjSubgroup h T) ⊔ conjSubgroup h T) :=
    hM2.to_sup_of_normal_left' hT2 hnorm
  have hyN1 : y ∈ Subgroup.normalizer ((conjSubgroup h T : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup hcfg'.wc₁ hS2 le_sup_right ?_)
    intro w hw
    have hz : y⁻¹ * w * y ∈ conjSubgroup h T := mem_conjSubgroup.1 hw
    have hm := hyZ'.2 _ (Subgroup.mem_sup_right hz)
    have e : w = (y⁻¹ * w * y) * ((y⁻¹ * w * y)⁻¹ * (y * (y⁻¹ * w * y) * y⁻¹)) := by group
    rw [e]
    exact (cfgM T (conjSubgroup h T) ⊔ conjSubgroup h T).mul_mem (Subgroup.mem_sup_right hz)
      (Subgroup.mem_sup_left hm)
  have hyT : y ∈ conjSubgroup g T := conjSubgroup_mono secA_le_left hyg
  have hyD : y ∈ classD T := mem_classD_of_mem_conjSubgroup hyT hy1
  have hcomm := conjSubgroup_secA_comm_of_mem_normalizer hP hS (k := h) hyD hyN1
  obtain ⟨a, haA, hane⟩ := hClaim y hyg hy1
  exact hane (hcomm a haA)

omit [Finite G] in
theorem secR₁_comm_of_gen_comm
    (h : ∀ i j : G, IsUIdx T T₁ i → IsUIdx T T₁ j → ∀ a ∈ conjSubgroup i (secA T T₁),
      ∀ x ∈ conjSubgroup j (secA T T₁), a * x = x * a) :
    ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x := by
  have hbot : ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
    rw [secR₁_eq_iSup_subtype]
    refine commutator_mem_of_forall_gen (T := ⊥) (fun i => ?_) (fun i j => ?_)
    · intro z hz
      exact mem_normalizer_of_conjSubgroup_eq (by
        have h2 : z ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro k
          simp only [Subgroup.mem_bot]
          constructor
          · rintro rfl
            simp
          · intro hk
            calc k = z⁻¹ * (z * k * z⁻¹) * z := by group
              _ = 1 := by rw [hk]; group
        exact mem_normalizer_iff_conjSubgroup_eq.1 h2)
    · intro a ha x hx
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact h i j i.2 j.2 a ha x hx
  intro x hx y hy'
  have := hbot x hx y hy'
  rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this

theorem secR₁_comm_of_card_lt (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    (hcard : Nat.card T < Nat.card (secA T T₁) * Nat.card (normIn T T₁)) :
    ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x :=
  secR₁_comm_of_gen_comm fun _ _ hi hj a ha x hx =>
    commute_conj_secA_conj_secA_of_card_lt h1 h3 hy hS hI hTO hBW hcard hj hi a ha x hx

end Six

end CFSG.CGT.Timmesfeld75
