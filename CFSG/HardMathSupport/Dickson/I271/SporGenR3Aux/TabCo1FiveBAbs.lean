module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Multi
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

section Perfect

theorem isPerfect_closure_pair {G : Type} [Group G] (x y : G)
    (hx : ∃ u ∈ Subgroup.closure ({x, y} : Set G), ∃ v ∈ Subgroup.closure ({x, y} : Set G),
      x = u * v * u⁻¹ * v⁻¹)
    (hy : ∃ u ∈ Subgroup.closure ({x, y} : Set G), ∃ v ∈ Subgroup.closure ({x, y} : Set G),
      y = u * v * u⁻¹ * v⁻¹) : Group.IsPerfect ↥(Subgroup.closure ({x, y} : Set G)) := by
  set L : Subgroup G := Subgroup.closure ({x, y} : Set G) with hL
  have key : ∀ a : ↥L, (∃ u ∈ L, ∃ v ∈ L, (a : G) = u * v * u⁻¹ * v⁻¹) → a ∈ commutator ↥L := by
    rintro a ⟨u, hu, v, hv, huv⟩
    have : a = ⁅(⟨u, hu⟩ : ↥L), (⟨v, hv⟩ : ↥L)⁆ :=
      Subtype.ext (by simpa [commutatorElement_def] using huv)
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have htop : (⊤ : Subgroup ↥L) ≤ commutator ↥L := by
    rw [← Subgroup.closure_closure_coe_preimage (k := ({x, y} : Set G))]
    refine (Subgroup.closure_le _).2 fun a ha => key a ?_
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha
    · obtain ⟨u, hu, v, hv, huv⟩ := hx
      exact ⟨u, hu, v, hv, ha.trans huv⟩
    · obtain ⟨u, hu, v, hv, huv⟩ := hy
      exact ⟨u, hu, v, hv, ha.trans huv⟩
  exact Group.isPerfect_def.2 (top_le_iff.1 htop)

theorem exists_noncomm_of_perfect {J : Type} [Group J] (hperf : Group.IsPerfect J)
    (hcard : 1 < Nat.card J) : ∃ a b : J, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : commutator J = ⊥ := by
    rw [eq_bot_iff, commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (h g₁ g₂)
  have htb : (⊤ : Subgroup J) = ⊥ := by
    rw [← Group.isPerfect_def.1 hperf]
    exact hc
  have : Nat.card J = 1 := by
    rw [← Subgroup.card_top (G := J), htb, Subgroup.card_bot]
  omega

end Perfect

section Conj

theorem closure_pair_conj {G : Type} [Group G] (τ x y : G) :
    Subgroup.closure ({τ * x * τ⁻¹, τ * y * τ⁻¹} : Set G) =
      (Subgroup.closure ({x, y} : Set G)).map (MulAut.conj τ).toMonoidHom := by
  rw [MonoidHom.map_closure, Set.image_pair]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem conj_mem_of_mem' {G : Type} [Group G] (R : Subgroup G) {s : G} (hs : s ∈ R) :
    (∀ e ∈ R, s * e * s⁻¹ ∈ R) ∧ (∀ e ∈ R, s⁻¹ * e * s ∈ R) :=
  ⟨fun _ he => R.mul_mem (R.mul_mem hs he) (R.inv_mem hs),
    fun _ he => R.mul_mem (R.mul_mem (R.inv_mem hs) he) hs⟩

theorem conj_closure_pair_of_commute {G : Type} [Group G] {R : Subgroup G} {a b s : G}
    (hR : R = Subgroup.closure ({a, b} : Set G)) (ha : Commute s a) (hb : Commute s b) :
    (∀ e ∈ R, s * e * s⁻¹ ∈ R) ∧ (∀ e ∈ R, s⁻¹ * e * s ∈ R) := by
  have hmem : ∀ t ∈ ({a, b} : Set G), t ∈ R := fun t ht => by
    rw [hR]
    exact Subgroup.subset_closure ht
  have hcomm : ∀ t ∈ ({a, b} : Set G), Commute s t := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht
    · rw [ht]
      exact ha
    · rw [ht]
      exact hb
  refine normalizes_of_gen hR (fun t ht => ?_) (fun t ht => ?_)
  · rw [(hcomm t ht).mul_inv_cancel]
    exact hmem t ht
  · have := (hcomm t ht).inv_left.mul_inv_cancel
    rw [inv_inv] at this
    rw [this]
    exact hmem t ht

end Conj

section Main

theorem multiShapeAt_A5A5_of_data {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hA : Good ↥(alternatingGroup (Fin 5))) (hRA : Rk ↥(alternatingGroup (Fin 5)))
    {G : Type} [Group G] (P : Subgroup G) [Finite P] (x : ↥P) (k x₁ y₁ τ : G)
    (hxk : (x : G) = k) (hk5 : k ^ 5 = 1) (hk1 : k ≠ 1) (hx₁ : x₁ ∈ P) (hy₁ : y₁ ∈ P)
    (hτ : τ ∈ P) (hkx₁ : k * x₁ = x₁ * k) (hky₁ : k * y₁ = y₁ * k) (hkτ : k * τ = τ * k)
    (hτ2 : τ * τ = 1) (hc₁ : x₁ * (τ * x₁ * τ⁻¹) = (τ * x₁ * τ⁻¹) * x₁)
    (hc₂ : x₁ * (τ * y₁ * τ⁻¹) = (τ * y₁ * τ⁻¹) * x₁)
    (hc₃ : y₁ * (τ * x₁ * τ⁻¹) = (τ * x₁ * τ⁻¹) * y₁)
    (hc₄ : y₁ * (τ * y₁ * τ⁻¹) = (τ * y₁ * τ⁻¹) * y₁)
    (hL : Nat.card ↥(Subgroup.closure ({x₁, y₁} : Set G)) = 60)
    (hX : ∃ u ∈ Subgroup.closure ({x₁, y₁} : Set G), ∃ v ∈ Subgroup.closure ({x₁, y₁} : Set G),
      x₁ = u * v * u⁻¹ * v⁻¹)
    (hY : ∃ u ∈ Subgroup.closure ({x₁, y₁} : Set G), ∃ v ∈ Subgroup.closure ({x₁, y₁} : Set G),
      y₁ = u * v * u⁻¹ * v⁻¹)
    (hEcard : Nat.card ↥(Subgroup.closure ({k, x₁, y₁, τ} : Set G)) = 36000)
    (hCbd : Nat.card ↥(Subgroup.centralizer ({k} : Set G) ⊓ P) ≤ 36000)
    (hpt : Nat.card ↥(Subgroup.centralizer ({k, x₁, y₁, τ * x₁ * τ⁻¹, τ * y₁ * τ⁻¹} : Set G) ⊓ P) ≤
      5) : MultiShapeAt 5 Good Rk x := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : G, x₂ = τ * x₁ * τ⁻¹ := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : G, y₂ = τ * y₁ * τ⁻¹ := ⟨_, rfl⟩
  rw [← hx₂] at hc₁ hc₃
  rw [← hy₂] at hc₂ hc₄
  rw [← hx₂, ← hy₂] at hpt
  have hkP : k ∈ P := hxk ▸ x.2
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hx₂P : x₂ ∈ P := by
    rw [hx₂]
    exact P.mul_mem (P.mul_mem hτ hx₁) (P.inv_mem hτ)
  have hy₂P : y₂ ∈ P := by
    rw [hy₂]
    exact P.mul_mem (P.mul_mem hτ hy₁) (P.inv_mem hτ)
  have hτx₂ : τ * x₂ * τ⁻¹ = x₁ := by
    rw [hx₂, hτi]
    calc τ * (τ * x₁ * τ) * τ = (τ * τ) * x₁ * (τ * τ) := by group
      _ = x₁ := by rw [hτ2, one_mul, mul_one]
  have hτy₂ : τ * y₂ * τ⁻¹ = y₁ := by
    rw [hy₂, hτi]
    calc τ * (τ * y₁ * τ) * τ = (τ * τ) * y₁ * (τ * τ) := by group
      _ = y₁ := by rw [hτ2, one_mul, mul_one]
  have cτk : Commute k τ := hkτ
  have ck₁ : Commute k x₁ := hkx₁
  have ck₂ : Commute k y₁ := hky₁
  have ckx₂ : Commute k x₂ := by
    rw [hx₂]
    exact (cτk.mul_right ck₁).mul_right cτk.inv_right
  have cky₂ : Commute k y₂ := by
    rw [hy₂]
    exact (cτk.mul_right ck₂).mul_right cτk.inv_right
  have c₁₂ : Commute x₁ x₂ := hc₁
  have c₁₂' : Commute x₁ y₂ := hc₂
  have c₂₁ : Commute y₁ x₂ := hc₃
  have c₂₂ : Commute y₁ y₂ := hc₄
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : Subgroup G, L₁ = Subgroup.closure ({x₁, y₁} : Set G) := ⟨_, rfl⟩
  obtain ⟨L₂, hL₂⟩ : ∃ L₂ : Subgroup G, L₂ = Subgroup.closure ({x₂, y₂} : Set G) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = Subgroup.closure ({k, x₁, y₁, x₂, y₂} : Set G) :=
    ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = Subgroup.closure ({k, x₁, y₁, τ} : Set G) := ⟨_, rfl⟩
  rw [← hL₁] at hL
  rw [← hC] at hEcard
  have mk : k ∈ E := by rw [hE]; exact Subgroup.subset_closure (by simp)
  have mx₁ : x₁ ∈ E := by rw [hE]; exact Subgroup.subset_closure (by simp)
  have my₁ : y₁ ∈ E := by rw [hE]; exact Subgroup.subset_closure (by simp)
  have mx₂ : x₂ ∈ E := by rw [hE]; exact Subgroup.subset_closure (by simp)
  have my₂ : y₂ ∈ E := by rw [hE]; exact Subgroup.subset_closure (by simp)
  have mx₁L : x₁ ∈ L₁ := by rw [hL₁]; exact Subgroup.subset_closure (by simp)
  have my₁L : y₁ ∈ L₁ := by rw [hL₁]; exact Subgroup.subset_closure (by simp)
  have mx₂L : x₂ ∈ L₂ := by rw [hL₂]; exact Subgroup.subset_closure (by simp)
  have my₂L : y₂ ∈ L₂ := by rw [hL₂]; exact Subgroup.subset_closure (by simp)
  obtain ⟨CG, hCG⟩ : ∃ CG : Subgroup G, CG = Subgroup.centralizer ({k} : Set G) ⊓ P := ⟨_, rfl⟩
  rw [← hCG] at hCbd
  have hmemCG : ∀ g, g ∈ P → g * k = k * g → g ∈ CG := fun g hg hc => by
    rw [hCG]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hc, hg⟩
  have hCGP : CG ≤ P := by rw [hCG]; exact inf_le_right
  haveI hfinCG : Finite ↥CG :=
    Finite.of_injective (Subgroup.inclusion hCGP) (Subgroup.inclusion_injective hCGP)
  have hCle : C ≤ CG := by
    rw [hC]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h | h <;> rw [h]
    · exact hmemCG _ hkP rfl
    · exact hmemCG _ hx₁ hkx₁.symm
    · exact hmemCG _ hy₁ hky₁.symm
    · exact hmemCG _ hτ hkτ.symm
  have hCeq : C = CG := Subgroup.eq_of_le_of_card_ge hCle (by rw [hEcard]; exact hCbd)
  have hEle : E ≤ CG := by
    rw [hE]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h | h | h <;> rw [h]
    · exact hmemCG _ hkP rfl
    · exact hmemCG _ hx₁ hkx₁.symm
    · exact hmemCG _ hy₁ hky₁.symm
    · exact hmemCG _ hx₂P ckx₂.symm
    · exact hmemCG _ hy₂P cky₂.symm
  have hτE : (∀ e ∈ E, τ * e * τ⁻¹ ∈ E) ∧ (∀ e ∈ E, τ⁻¹ * e * τ ∈ E) := by
    have h1 : ∀ t ∈ ({k, x₁, y₁, x₂, y₂} : Set G), τ * t * τ⁻¹ ∈ E := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with h | h | h | h | h <;> rw [h]
      · rw [cτk.symm.mul_inv_cancel]
        exact mk
      · rw [← hx₂]
        exact mx₂
      · rw [← hy₂]
        exact my₂
      · rw [hτx₂]
        exact mx₁
      · rw [hτy₂]
        exact my₁
    refine normalizes_of_gen hE h1 fun t ht => ?_
    have := h1 t ht
    rw [hτi] at this ⊢
    exact this
  have hconjE : ∀ s ∈ ({k, x₁, y₁, τ} : Set G),
      (∀ e ∈ E, s * e * s⁻¹ ∈ E) ∧ (∀ e ∈ E, s⁻¹ * e * s ∈ E) := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with h | h | h | h <;> rw [h]
    · exact conj_mem_of_mem' E mk
    · exact conj_mem_of_mem' E mx₁
    · exact conj_mem_of_mem' E my₁
    · exact hτE
  have hEn : ∀ g ∈ CG, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    rw [← hCeq, hC] at hg
    exact (normalizes_closure hconjE g hg).1 e he
  have h₁E : L₁ ≤ E := by
    rw [hL₁]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h <;> rw [h]
    · exact mx₁
    · exact my₁
  have h₂E : L₂ ≤ E := by
    rw [hL₂]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h <;> rw [h]
    · exact mx₂
    · exact my₂
  have h₁n : ∀ g ∈ E, ∀ l ∈ L₁, g * l * g⁻¹ ∈ L₁ := by
    intro g hg l hl
    rw [hE] at hg
    refine (normalizes_closure (S := ({k, x₁, y₁, x₂, y₂} : Set G)) (R := L₁) ?_ g hg).1 l hl
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with h | h | h | h | h <;> rw [h]
    · exact conj_closure_pair_of_commute hL₁ ck₁ ck₂
    · exact conj_mem_of_mem' L₁ mx₁L
    · exact conj_mem_of_mem' L₁ my₁L
    · exact conj_closure_pair_of_commute hL₁ c₁₂.symm c₂₁.symm
    · exact conj_closure_pair_of_commute hL₁ c₁₂'.symm c₂₂.symm
  have h₂n : ∀ g ∈ E, ∀ l ∈ L₂, g * l * g⁻¹ ∈ L₂ := by
    intro g hg l hl
    rw [hE] at hg
    refine (normalizes_closure (S := ({k, x₁, y₁, x₂, y₂} : Set G)) (R := L₂) ?_ g hg).1 l hl
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with h | h | h | h | h <;> rw [h]
    · exact conj_closure_pair_of_commute hL₂ ckx₂ cky₂
    · exact conj_closure_pair_of_commute hL₂ c₁₂ c₁₂'
    · exact conj_closure_pair_of_commute hL₂ c₂₁ c₂₂
    · exact conj_mem_of_mem' L₂ mx₂L
    · exact conj_mem_of_mem' L₂ my₂L
  have hL₁P : L₁ ≤ P := fun l hl => hCGP (hEle (h₁E hl))
  have hL₂P : L₂ ≤ P := fun l hl => hCGP (hEle (h₂E hl))
  haveI : Finite ↥L₁ := Finite.of_injective (Subgroup.inclusion hL₁P)
    (Subgroup.inclusion_injective hL₁P)
  haveI : Finite ↥L₂ := Finite.of_injective (Subgroup.inclusion hL₂P)
    (Subgroup.inclusion_injective hL₂P)
  have hperf : Group.IsPerfect ↥L₁ := by
    rw [hL₁]
    exact isPerfect_closure_pair x₁ y₁ hX hY
  have hs₁ : IsSimpleGroup ↥L₁ := CFSG.Quasithin.A312J2.isSimpleGroup_of_perfect_card_sixty hperf hL
  have hnab₁ : ∃ a b : ↥L₁, a * b ≠ b * a :=
    exists_noncomm_of_perfect hperf (by rw [hL]; norm_num)
  obtain ⟨eA⟩ := CFSG.Quasithin.A312J2.nonempty_mulEquiv_alt5_of_perfect hperf hL
  have hmap : L₂ = L₁.map (MulAut.conj τ).toMonoidHom := by
    rw [hL₂, hL₁, hx₂, hy₂]
    exact closure_pair_conj τ x₁ y₁
  let eL : ↥L₁ ≃* ↥L₂ :=
    (L₁.equivMapOfInjective (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr hmap.symm)
  have hs₂ : IsSimpleGroup ↥L₂ := eL.isSimpleGroup_congr.1 hs₁
  have hnab₂ : ∃ a b : ↥L₂, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab₁
    exact ⟨eL a, eL b, fun h => hab (by simpa using congrArg eL.symm h)⟩
  have hp₁ : 5 ∣ Nat.card ↥L₁ := by rw [hL]; norm_num
  have hp₂ : 5 ∣ Nat.card ↥L₂ := by
    rw [← Nat.card_congr eL.toEquiv, hL]
    norm_num
  have hL₁k : L₁ ≤ Subgroup.centralizer ({k} : Set G) := by
    rw [hL₁]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h <;> rw [h]
    · exact Subgroup.mem_centralizer_singleton_iff.2 hkx₁.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hky₁.symm
  have hL₂k : L₂ ≤ Subgroup.centralizer ({k} : Set G) := by
    rw [hL₂]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h <;> rw [h]
    · exact Subgroup.mem_centralizer_singleton_iff.2 ckx₂.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 cky₂.symm
  have hcent : IsPGroup 5 ↥(Subgroup.centralizer ({k} : Set G) ⊓ P ⊓
      Subgroup.centralizer (L₁ : Set G) ⊓ Subgroup.centralizer (L₂ : Set G)) := by
    obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = Subgroup.centralizer ({k} : Set G) ⊓ P ⊓
      Subgroup.centralizer (L₁ : Set G) ⊓ Subgroup.centralizer (L₂ : Set G) := ⟨_, rfl⟩
    rw [← hD]
    obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = Subgroup.centralizer
        ({k, x₁, y₁, x₂, y₂} : Set G) ⊓ P := ⟨_, rfl⟩
    rw [← hT] at hpt
    haveI : Finite ↥T := by
      have hle : T ≤ P := by rw [hT]; exact inf_le_right
      exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hDT : D ≤ T := by
      intro d hd
      rw [hD] at hd
      obtain ⟨hd', hd3⟩ := Subgroup.mem_inf.1 hd
      obtain ⟨hd'', hd2⟩ := Subgroup.mem_inf.1 hd'
      obtain ⟨hd1, hdP⟩ := Subgroup.mem_inf.1 hd''
      rw [hT]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_, hdP⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with h' | h' | h' | h' | h' <;> rw [h']
      · exact (Subgroup.mem_centralizer_singleton_iff.1 hd1).symm
      · exact Subgroup.mem_centralizer_iff.1 hd2 _ mx₁L
      · exact Subgroup.mem_centralizer_iff.1 hd2 _ my₁L
      · exact Subgroup.mem_centralizer_iff.1 hd3 _ mx₂L
      · exact Subgroup.mem_centralizer_iff.1 hd3 _ my₂L
    have hkD : k ∈ D := by
      rw [hD]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hkP⟩, ?_⟩, ?_⟩
      · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        exact Subgroup.mem_centralizer_singleton_iff.1 (hL₁k hh)
      · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        exact Subgroup.mem_centralizer_singleton_iff.1 (hL₂k hh)
    have hord : orderOf k = 5 := orderOf_eq_prime hk5 hk1
    have hzD : Subgroup.zpowers k ≤ D := Subgroup.zpowers_le.2 hkD
    have h5 : 5 ∣ Nat.card D := by
      have := Subgroup.card_dvd_of_le hzD
      rwa [Nat.card_zpowers, hord] at this
    have hDle5 : Nat.card D ≤ 5 := (Subgroup.card_le_of_le hDT).trans hpt
    haveI : Finite ↥D :=
      Finite.of_injective (Subgroup.inclusion hDT) (Subgroup.inclusion_injective hDT)
    have hDpos : 0 < Nat.card D := Nat.card_pos
    exact IsPGroup.of_card (n := 1)
      (by rw [pow_one]; exact le_antisymm hDle5 (Nat.le_of_dvd hDpos h5))
  have hEle' : E ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
    rw [hxk, ← hCG]
    exact hEle
  have hEn' : ∀ g ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    rw [hxk, ← hCG]
    exact hEn
  have hcent' : IsPGroup 5 ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ P ⊓
      Subgroup.centralizer (L₁ : Set G) ⊓ Subgroup.centralizer (L₂ : Set G)) := by
    rw [hxk]
    exact hcent
  exact multiShapeAt_of_subgroup_data_two (p := 5) Nat.prime_five (by norm_num) hGood hRk P x E L₁
    L₂ hEle' hEn' h₁E h₂E h₁n h₂n hs₁ hs₂ hnab₁ hnab₂ hp₁ hp₂ hcent'
    (hGood _ _ eA.symm hA) (hRk _ _ eA.symm hRA) (hGood _ _ (eA.symm.trans eL) hA)
    (hRk _ _ (eA.symm.trans eL) hRA)

end Main

end CFSG.HardMathSupport.Dickson.I271.TabCo1
