module

public import CFSG.CGT.Timmesfeld75.Sec5FiveBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Generic

variable {Γ : Type*} [Group Γ]

theorem IsWC.commutator_mem_of_commute {V : Subgroup Γ} (hV : IsWC V) {a b : Γ} (ha : a ∈ V)
    (ha1 : a ≠ 1) (hc : ∀ x ∈ V, Commute x ⁅a, b⁆) : ⁅a, b⁆ ∈ V := by
  have hba : b * a * b⁻¹ = ⁅a, b⁆⁻¹ * a := by
    simp only [commutatorElement_def]
    group
  have hle : conjSubgroup b⁻¹ V ≤ Subgroup.centralizer ({a} : Set Γ) := by
    intro y hy
    have hy' : b * y * b⁻¹ ∈ V := by
      rw [mem_conjSubgroup, inv_inv] at hy
      exact hy
    have h1 : (b * y * b⁻¹) * (b * a * b⁻¹) = (b * a * b⁻¹) * (b * y * b⁻¹) := by
      rw [hba]
      exact ((hc _ hy').inv_right).mul_right (elemAbelian_mul_comm hV.1 hy' ha)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc y * a = b⁻¹ * ((b * y * b⁻¹) * (b * a * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * a * b⁻¹) * (b * y * b⁻¹)) * b := by rw [h1]
      _ = a * y := by group
  have hconj : conjSubgroup b⁻¹ V = V := (hV.2 a ha ha1).2 b⁻¹ hle
  have hmem : b * a * b⁻¹ ∈ V := by
    have h1 : a ∈ conjSubgroup b⁻¹ V := by
      rw [hconj]
      exact ha
    rw [mem_conjSubgroup, inv_inv] at h1
    exact h1
  rw [hba] at hmem
  have h2 : ⁅a, b⁆⁻¹ ∈ V := by
    have h3 := V.mul_mem hmem (V.inv_mem ha)
    simpa using h3
  simpa using V.inv_mem h2

end Generic

section Gen

variable {G : Type} [Group G] {T : Subgroup G}

theorem bar_comm_of_commutator_mem {x y : G} (hx : x ∈ Subgroup.normalizer (T : Set G))
    (hy : y ∈ Subgroup.normalizer (T : Set G)) (h : ⁅x, y⁆ ∈ T) :
    barElt T hx * barElt T hy = barElt T hy * barElt T hx := by
  have hxy : ⁅x, y⁆ ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer h
  have h1 : barElt T hxy = 1 := (barElt_eq_one_iff hxy).2 h
  rw [barElt_commutator hx hy hxy] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem barElt_pow {x : G} (hx : x ∈ Subgroup.normalizer (T : Set G)) (n : ℕ) :
    barElt T hx ^ n = barElt T ((Subgroup.normalizer (T : Set G)).pow_mem hx n) := by
  unfold barElt
  rw [← QuotientGroup.mk_pow]
  rfl

theorem commutator_mem_of_forall_gen {ι : Type*} {S : ι → Subgroup G}
    (hSN : ∀ i, S i ≤ Subgroup.normalizer (T : Set G))
    (h : ∀ i j, ∀ x ∈ S i, ∀ y ∈ S j, ⁅x, y⁆ ∈ T) :
    ∀ x ∈ ⨆ i, S i, ∀ y ∈ ⨆ i, S i, ⁅x, y⁆ ∈ T := by
  have step1 : ∀ i, ∀ x ∈ S i, ∀ y ∈ ⨆ j, S j, ⁅x, y⁆ ∈ T := by
    intro i x hx y hy
    have key : y ∈ Subgroup.normalizer (T : Set G) ∧ ⁅x, y⁆ ∈ T := by
      refine Subgroup.iSup_induction S
        (C := fun y => y ∈ Subgroup.normalizer (T : Set G) ∧ ⁅x, y⁆ ∈ T) hy ?_ ?_ ?_
      · intro j y hyj
        exact ⟨hSN j hyj, h i j x hx y hyj⟩
      · exact ⟨one_mem _, by simp [T.one_mem]⟩
      · rintro y₁ y₂ ⟨hy₁N, hy₁⟩ ⟨hy₂N, hy₂⟩
        refine ⟨mul_mem hy₁N hy₂N, ?_⟩
        have e : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact T.mul_mem hy₁ (conj_mem_of_mem_normalizer hy₁N hy₂)
    exact key.2
  intro x hx y hy
  have key : x ∈ Subgroup.normalizer (T : Set G) ∧ ⁅x, y⁆ ∈ T := by
    refine Subgroup.iSup_induction S
      (C := fun x => x ∈ Subgroup.normalizer (T : Set G) ∧ ⁅x, y⁆ ∈ T) hx ?_ ?_ ?_
    · intro i x hxi
      exact ⟨hSN i hxi, step1 i x hxi y hy⟩
    · exact ⟨one_mem _, by simp [T.one_mem]⟩
    · rintro x₁ x₂ ⟨hx₁N, hx₁⟩ ⟨hx₂N, hx₂⟩
      refine ⟨mul_mem hx₁N hx₂N, ?_⟩
      have e : ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact T.mul_mem (conj_mem_of_mem_normalizer hx₁N hx₂) hx₁
  exact key.2

theorem isPGroup_two_iSup_of_commutator {ι : Type*} {S : ι → Subgroup G}
    (hT : IsElemAbelian 2 T) (hSN : ∀ i, S i ≤ Subgroup.normalizer (T : Set G))
    (hS2 : ∀ i, ∀ x ∈ S i, x * x = 1)
    (h : ∀ x ∈ ⨆ i, S i, ∀ y ∈ ⨆ i, S i, ⁅x, y⁆ ∈ T) :
    IsPGroup 2 ↥(⨆ i, S i) := by
  have hUN : (⨆ i, S i) ≤ Subgroup.normalizer (T : Set G) := iSup_le hSN
  have key : ∀ x (hx : x ∈ ⨆ i, S i), ∃ k : ℕ, barElt T (hUN hx) ^ (2 ^ k) = 1 := by
    intro x hx
    refine Subgroup.iSup_induction' S (C := fun x hx => ∃ k : ℕ, barElt T (hUN hx) ^ (2 ^ k) = 1)
      ?_ ?_ ?_ hx
    · intro i x hxi
      refine ⟨1, ?_⟩
      rw [barElt_pow, barElt_eq_one_iff]
      have : x ^ (2 ^ 1) = 1 := by rw [pow_one, pow_two]; exact hS2 i x hxi
      rw [this]
      exact T.one_mem
    · exact ⟨0, by simp [barElt_one]⟩
    · rintro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      have hcomm : barElt T (hUN hx) * barElt T (hUN hy) = barElt T (hUN hy) * barElt T (hUN hx) :=
        bar_comm_of_commutator_mem (hUN hx) (hUN hy) (h x hx y hy)
      have hxy : barElt T (hUN (mul_mem hx hy)) = barElt T (hUN hx) * barElt T (hUN hy) :=
        (barElt_mul (hUN hx) (hUN hy)).symm
      rw [hxy, (Commute.mul_pow hcomm (2 ^ (a + b)))]
      have h1 : barElt T (hUN hx) ^ (2 ^ (a + b)) = 1 := by
        rw [pow_add, pow_mul, ha, one_pow]
      have h2 : barElt T (hUN hy) ^ (2 ^ (a + b)) = 1 := by
        rw [add_comm, pow_add, pow_mul, hb, one_pow]
      rw [h1, h2, one_mul]
  intro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := key x hx
  refine ⟨k + 1, Subtype.ext ?_⟩
  have h1 : x ^ (2 ^ k) ∈ T := by
    rw [← barElt_eq_one_iff ((Subgroup.normalizer (T : Set G)).pow_mem (hUN hx) _),
      ← barElt_pow]
    exact hk
  have h2 := hT.2 _ h1
  show x ^ (2 ^ (k + 1)) = 1
  rw [pow_succ, pow_mul]
  exact h2

end Gen

section R1

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem le_hSubU_of_isUIdx {h : G} (hu : IsUIdx T T₁ h) :
    normIn (conjSubgroup h T) T ≤ hSubU T T₁ :=
  le_sup_of_le_right
    (le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => normIn (conjSubgroup h T) T) h hu)

theorem left_le_hSubU : T ≤ hSubU T T₁ := le_sup_left

theorem secR₁_eq_iSup_subtype :
    secR₁ T T₁ = ⨆ h : {h : G // IsUIdx T T₁ h}, conjSubgroup (h : G) (secA T T₁) :=
  iSup_subtype' (p := fun h => IsUIdx T T₁ h) (f := fun h _ => conjSubgroup h (secA T T₁))

variable [Finite G]

theorem IsUIdx.conj_secA_le (hP : MaxPair T T₁) (hS : Sec3Global T) {h : G}
    (hu : IsUIdx T T₁ h) :
    conjSubgroup h (secA T T₁) ≤ normIn (conjSubgroup h T) T :=
  conjSubgroup_secA_le_normIn hP hS hu.1 (hu.normIn_conj_ne_bot hP)

theorem IsUIdx.conj_secA_le_normalizer (hP : MaxPair T T₁) (hS : Sec3Global T) {h : G}
    (hu : IsUIdx T T₁ h) :
    conjSubgroup h (secA T T₁) ≤ Subgroup.normalizer (T : Set G) := fun _ hx =>
  (mem_normIn.1 (hu.conj_secA_le hP hS hx)).2

theorem secR₁_le_normalizer (hP : MaxPair T T₁) (hS : Sec3Global T) :
    secR₁ T T₁ ≤ Subgroup.normalizer (T : Set G) := by
  rw [secR₁_eq_iSup_subtype]
  exact iSup_le fun i => i.2.conj_secA_le_normalizer hP hS

theorem conjSubgroup_secR₁ {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup n (secR₁ T T₁) = secR₁ T T₁ := by
  have key : ∀ n ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup n (secR₁ T T₁) ≤ secR₁ T T₁ := by
    intro n hn
    rw [conjSubgroup_le_iff, secR₁]
    refine iSup₂_le fun h hu => ?_
    rw [← conjSubgroup_le_iff]
    have h1 : conjSubgroup n (conjSubgroup h (secA T T₁)) ≤ secR₁ T T₁ := by
      rw [conjSubgroup_conjSubgroup]
      exact le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁))
        (n * h) (hu.mul_normalizer hn)
    exact h1
  exact conjSubgroup_eq_of_le (key n hn)

theorem commutator_conj_secA_mem (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T) (hA4 : secA T T₁ ≠ normIn T T₁) {g h : G}
    (hg : IsUIdx T T₁ g) (hh : IsUIdx T T₁ h) :
    ∀ a ∈ conjSubgroup g (secA T T₁), ∀ b ∈ conjSubgroup h (secA T T₁), ⁅a, b⁆ ∈ T := by
  intro a ha b hb
  have hP := hy.pair
  by_cases ha1 : a = 1
  · rw [ha1]
    simp [T.one_mem]
  by_cases hA1 : secA T T₁ = ⊥
  · exact absurd ((conjSubgroup_eq_bot_iff.2 hA1 : conjSubgroup g (secA T T₁) = ⊥) ▸ ha |>
      Subgroup.mem_bot.1) ha1
  have hT4 : 4 < Nat.card T := by
    have hsec := hP.sec3 hS
    have hAL : secA T T₁ < normIn T T₁ := lt_of_le_of_ne secA_le_normIn hA4
    have hLT : normIn T T₁ < T := hsec.cfg.normIn_lt hP.conj
    have hc1 := Subgroup.card_lt_of_lt hAL
    have hc2 := Subgroup.card_lt_of_lt hLT
    have hA2 : 1 < Nat.card (secA T T₁) := (Subgroup.one_lt_card_iff_ne_bot _).2 hA1
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (normIn_le T T₁)
    have hpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
    rcases k with _ | _ | k
    · omega
    · omega
    · rw [hk]
      nlinarith
  have hgN := hg.conj_secA_le_normalizer hP hS
  have hhN := hh.conj_secA_le_normalizer hP hS
  have haN : a ∈ Subgroup.normalizer (T : Set G) := hgN ha
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := hhN hb
  have hcT : ∀ t ∈ T, ⁅a, b⁆ * t = t * ⁅a, b⁆ := fun t ht => by
    have := commutator_conj_secA_le_centralizer hP hS hI hg hh
      (Subgroup.commutator_mem_commutator ha hb)
    exact (Subgroup.mem_centralizer_iff.1 this t ht).symm
  have hcN : ⁅a, b⁆ ∈ Subgroup.normalizer (T : Set G) := by
    have := (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem haN hbN)
        ((Subgroup.normalizer (T : Set G)).inv_mem haN))
      ((Subgroup.normalizer (T : Set G)).inv_mem hbN)
    simpa [commutatorElement_def] using this
  have hcP : ⁅a, b⁆ ∈ hSubU T T₁ := by
    have haP : a ∈ hSubU T T₁ := le_hSubU_of_isUIdx hg (hg.conj_secA_le hP hS ha)
    have hbP : b ∈ hSubU T T₁ := le_hSubU_of_isUIdx hh (hh.conj_secA_le hP hS hb)
    simpa [commutatorElement_def] using (hSubU T T₁).mul_mem
      ((hSubU T T₁).mul_mem ((hSubU T T₁).mul_mem haP hbP) ((hSubU T T₁).inv_mem haP))
      ((hSubU T T₁).inv_mem hbP)
  have hcen := h3 G T T₁ hy hS hI hT4 ⁅a, b⁆ hcP hcT
  have hWC : IsWC (barSub T (normIn (conjSubgroup g T) T)) :=
    sec48_of_noA h1 G T (conjSubgroup g T) (hg.stepHyp hy hS) hS hI
  have haL : a ∈ normIn (conjSubgroup g T) T := hg.conj_secA_le hP hS ha
  have hTa : a ∉ T := fun haT => ha1 (by
    have : a ∈ T ⊓ conjSubgroup g T := ⟨haT, (mem_normIn.1 haL).1⟩
    rwa [hP.wc.inf_conj_eq_bot hg.1, Subgroup.mem_bot] at this)
  have hbarmem : barElt T hcN ∈ barSub T (normIn (conjSubgroup g T) T) := by
    rw [barElt_commutator haN hbN hcN]
    refine hWC.commutator_mem_of_commute (barElt_mem_barSub haN haL)
      (fun h' => hTa ((barElt_eq_one_iff haN).1 h')) fun x hx => ?_
    obtain ⟨u, huN, huL, rfl⟩ := exists_eq_barElt_of_mem_barSub hx
    have := bar_comm_of_commutator_mem hcN huN
      (hcen u (le_hSubU_of_isUIdx hg huL))
    rw [barElt_commutator haN hbN hcN] at this
    exact this.symm
  obtain ⟨u, huN, huL, hus⟩ := (barElt_mem_barSub_iff hcN).1 hbarmem
  obtain ⟨s, hsdef⟩ : ∃ s, s = u⁻¹ * ⁅a, b⁆ := ⟨_, rfl⟩
  rw [← hsdef] at hus
  have hcs : ⁅a, b⁆ = u * s := by rw [hsdef]; group
  have huT : ∀ t ∈ T, u * t = t * u := by
    intro t ht
    have hu' : u = ⁅a, b⁆ * s⁻¹ := by rw [hsdef]; group
    calc u * t = ⁅a, b⁆ * (s⁻¹ * t) := by rw [hu', mul_assoc]
      _ = ⁅a, b⁆ * (t * s⁻¹) := by rw [elemAbelian_mul_comm hP.wc.1 (T.inv_mem hus) ht]
      _ = (⁅a, b⁆ * t) * s⁻¹ := by rw [mul_assoc]
      _ = (t * ⁅a, b⁆) * s⁻¹ := by rw [hcT t ht]
      _ = t * (⁅a, b⁆ * s⁻¹) := by rw [mul_assoc]
      _ = t * u := by rw [hu']
  by_cases hu1 : u = 1
  · rw [hcs, hu1, one_mul]
    exact hus
  · exfalso
    have hcfg := (hg.sec3 hP hS).cfg
    have hTC : T ≤ Subgroup.centralizer ({u} : Set G) := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2 (huT t ht).symm
    have heq := hcfg.inf_centralizer_eq_normIn huL hu1
    rw [inf_eq_left.2 hTC] at heq
    have hlt := hcfg.normIn_lt (⟨g, rfl⟩ : ∃ x : G, conjSubgroup g T = conjSubgroup x T)
    rw [← heq] at hlt
    exact lt_irrefl _ hlt

theorem commutator_secR₁_mem (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T) (hA4 : secA T T₁ ≠ normIn T T₁) :
    ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, ⁅x, y⁆ ∈ T := by
  rw [secR₁_eq_iSup_subtype]
  refine commutator_mem_of_forall_gen (fun i => i.2.conj_secA_le_normalizer hy.pair hS)
    fun i j => ?_
  exact commutator_conj_secA_mem h1 h3 hy hS hI hA4 i.2 j.2

theorem isPGroup_secR₁ (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T) (hA4 : secA T T₁ ≠ normIn T T₁) :
    IsPGroup 2 ↥(secR₁ T T₁) := by
  have hP := hy.pair
  have hcomm := commutator_secR₁_mem h1 h3 hy hS hI hA4
  rw [secR₁_eq_iSup_subtype] at hcomm ⊢
  refine isPGroup_two_iSup_of_commutator hP.wc.1 (fun i => i.2.conj_secA_le_normalizer hP hS)
    (fun i x hx => ?_) hcomm
  have hxT : x ∈ conjSubgroup (i : G) T := conjSubgroup_mono secA_le_left hx
  exact elemAbelian_mul_self (isElemAbelian_conjSubgroup hP.wc.1 i) hxT

end R1

end CFSG.CGT.Timmesfeld75
