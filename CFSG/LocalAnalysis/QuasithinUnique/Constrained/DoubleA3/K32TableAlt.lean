module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableA4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAut

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Perfect

variable {K : Type} [Group K]

theorem k32_comm_center_left (c : K) (hc : c ∈ Subgroup.center K) (x y : K) :
    ⁅c * x, y⁆ = ⁅x, y⁆ := by
  have h1 : (x * y * x⁻¹) * c⁻¹ = c⁻¹ * (x * y * x⁻¹) :=
    Subgroup.mem_center_iff.mp (inv_mem hc) _
  rw [commutatorElement_def, commutatorElement_def]
  calc c * x * y * (c * x)⁻¹ * y⁻¹ = c * ((x * y * x⁻¹) * c⁻¹) * y⁻¹ := by group
    _ = c * (c⁻¹ * (x * y * x⁻¹)) * y⁻¹ := by rw [h1]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem k32_comm_center_right (c : K) (hc : c ∈ Subgroup.center K) (x y : K) :
    ⁅x, c * y⁆ = ⁅x, y⁆ := by
  have h1 : (y⁻¹) * c⁻¹ = c⁻¹ * y⁻¹ := Subgroup.mem_center_iff.mp (inv_mem hc) _
  have h2 : x * (c * y) = c * (x * y) := by
    have := Subgroup.mem_center_iff.mp hc x
    calc x * (c * y) = (x * c) * y := by group
      _ = (c * x) * y := by rw [this]
      _ = c * (x * y) := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (c * y) * x⁻¹ * (c * y)⁻¹ = (c * (x * y)) * x⁻¹ * (y⁻¹ * c⁻¹) := by rw [h2]; group
    _ = c * (x * y * x⁻¹ * (y⁻¹ * c⁻¹)) := by group
    _ = c * (x * y * x⁻¹ * (c⁻¹ * y⁻¹)) := by rw [h1]
    _ = x * y * x⁻¹ * y⁻¹ := by
      have h3 : (x * y * x⁻¹) * c⁻¹ = c⁻¹ * (x * y * x⁻¹) :=
        Subgroup.mem_center_iff.mp (inv_mem hc) _
      calc c * (x * y * x⁻¹ * (c⁻¹ * y⁻¹)) = c * (((x * y * x⁻¹) * c⁻¹) * y⁻¹) := by group
        _ = c * ((c⁻¹ * (x * y * x⁻¹)) * y⁻¹) := by rw [h3]
        _ = x * y * x⁻¹ * y⁻¹ := by group

theorem k32_eq_one_of_trivial_mod_center [Group.IsPerfect K] (γ : MulAut K)
    (h : ∀ k, γ k * k⁻¹ ∈ Subgroup.center K) : γ = 1 := by
  have hfix : ∀ a b : K, γ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨za, hza, hza'⟩ : ∃ za ∈ Subgroup.center K, γ a = za * a :=
      ⟨γ a * a⁻¹, h a, by group⟩
    obtain ⟨zb, hzb, hzb'⟩ : ∃ zb ∈ Subgroup.center K, γ b = zb * b :=
      ⟨γ b * b⁻¹, h b, by group⟩
    have e1 : γ ⁅a, b⁆ = ⁅γ a, γ b⁆ := map_commutatorElement γ.toMonoidHom a b
    rw [e1, hza', hzb', k32_comm_center_left za hza, k32_comm_center_right zb hzb]
  have hle : commutator K ≤ MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id K) := by
    rw [commutator_def, Subgroup.commutator_def]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, -, b, -, rfl⟩
    exact hfix a b
  have htop := Group.IsPerfect.commutator_eq_top (G := K)
  ext k
  have hk : k ∈ MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id K) :=
    hle (htop ▸ Subgroup.mem_top k)
  exact hk

theorem k32_conj_ker : (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
  ext k
  simp only [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun φ : MulAut K => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * k = (k * g * k⁻¹) * k := by rw [this]
      _ = k * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc k * g * k⁻¹ = (g * k) * k⁻¹ := by rw [← h g]
      _ = g := by group

theorem k32_center_map_eq (α : MulAut K) :
    (Subgroup.center K).map α.toMonoidHom = Subgroup.center K := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩ g
    have := hz (α.symm g)
    have := congrArg α this
    simpa using this
  · intro hx
    refine ⟨α.symm x, ?_, by simp⟩
    intro g
    have := hx (α g)
    have := congrArg α.symm this
    simpa using this

@[expose] def k32AutQuot (K : Type) [Group K] : MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun α := QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) α (k32_center_map_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H z => rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H z => rfl

theorem k32AutQuot_injective [Group.IsPerfect K] : Function.Injective (k32AutQuot K) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  apply k32_eq_one_of_trivial_mod_center
  intro k
  have h1 : ((α k : K) : K ⧸ Subgroup.center K) = (k : K ⧸ Subgroup.center K) :=
    congrArg (fun φ : MulAut (K ⧸ Subgroup.center K) => φ (k : K ⧸ Subgroup.center K)) hα
  have h2 : (α k)⁻¹ * k ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq]
    exact h1
  have hw : ∀ g : K, g * ((α k)⁻¹ * k)⁻¹ = ((α k)⁻¹ * k)⁻¹ * g :=
    Subgroup.mem_center_iff.mp (inv_mem h2)
  have h3 : α k * k⁻¹ = ((α k)⁻¹ * k)⁻¹ := by
    calc α k * k⁻¹ = α k * ((α k)⁻¹ * k)⁻¹ * (α k)⁻¹ := by group
      _ = ((α k)⁻¹ * k)⁻¹ * α k * (α k)⁻¹ := by rw [hw (α k)]
      _ = ((α k)⁻¹ * k)⁻¹ := by group
  rw [h3]
  exact inv_mem h2

end Perfect

section Counting

variable {K : Type} [Group K] [Finite K]

theorem k32_card_mulAut_le [Group.IsPerfect K] :
    Nat.card (MulAut K) ≤ Nat.card (MulAut (K ⧸ Subgroup.center K)) :=
  Nat.card_le_card_of_injective _ k32AutQuot_injective

omit [Finite K] in
theorem k32_card_innAut : Nat.card (innAut K) = Nat.card (K ⧸ Subgroup.center K) := by
  have e1 := QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)
  have e2 := QuotientGroup.quotientMulEquivOfEq (k32_conj_ker (K := K))
  calc Nat.card (innAut K)
      = Nat.card (K ⧸ (MulAut.conj : K →* MulAut K).ker) := (Nat.card_congr e1.toEquiv).symm
    _ = Nat.card (K ⧸ Subgroup.center K) := Nat.card_congr e2.toEquiv

end Counting

section AltFacts

theorem k32_card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem k32_card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem k32_card_mulAut_alt7 : Nat.card (MulAut (alternatingGroup (Fin 7))) = 5040 := by
  have hc : Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7))) :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)
  have hperm : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  rw [← Nat.card_congr (Equiv.ofBijective _ hc)]
  exact hperm

end AltFacts

section Main

theorem k32AltOut_proved : K32AltOut := by
  intro K _ _ hq hCQ A V hA
  have hperf : Group.IsPerfect K := hq.1
  by_contra hne
  have hVJ : V ⊓ innAut K = ⊥ := hne
  have hJn : (innAut K).Normal := innAut_normal K
  have hAJ : A ≤ Subgroup.normalizer ((innAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.normalizer_eq_top (innAut K)]
    exact le_top
  have hAJbot : A ⊓ innAut K = ⊥ := by
    by_contra hAJne
    have hnorm : A ≤ Subgroup.normalizer ((A ⊓ innAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨A.mul_mem (A.mul_mem ha hy1) (A.inv_mem ha), hJn.conj_mem y hy2 a⟩
      · rintro ⟨hy1, hy2⟩
        refine ⟨?_, ?_⟩
        · have := A.mul_mem (A.mul_mem (A.inv_mem ha) hy1) ha
          simpa [mul_assoc] using this
        · have := hJn.conj_mem _ hy2 a⁻¹
          simpa [mul_assoc] using this
    have hVle : V ≤ A ⊓ innAut K := k32_le_of_normal_ne_bot hA inf_le_left hnorm hAJne
    have hVJ' : V ≤ innAut K := hVle.trans inf_le_right
    have : V ⊓ innAut K = V := inf_eq_left.mpr hVJ'
    rw [this] at hVJ
    have h4 := hA.card_U
    rw [hVJ, Subgroup.card_bot] at h4
    omega
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hAJ
  rw [hAJbot, Subgroup.card_bot, mul_one, hA.card_L] at hmul
  have hle1 : Nat.card ↥(A ⊔ innAut K) ≤ Nat.card (MulAut K) := Subgroup.card_le_card_group _
  have hle2 := k32_card_mulAut_le (K := K)
  rw [k32_card_innAut] at hmul
  rcases hCQ with he | he
  · obtain ⟨e⟩ := he
    have hK : Nat.card (K ⧸ Subgroup.center K) = 360 := by
      rw [Nat.card_congr e.toEquiv]; exact k32_card_alt6
    have hAut : Nat.card (MulAut (K ⧸ Subgroup.center K)) ≤ 1440 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    omega
  · obtain ⟨e⟩ := he
    have hK : Nat.card (K ⧸ Subgroup.center K) = 2520 := by
      rw [Nat.card_congr e.toEquiv]; exact k32_card_alt7
    have hAut : Nat.card (MulAut (K ⧸ Subgroup.center K)) = 5040 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact k32_card_mulAut_alt7
    omega

end Main

end CFSG.QuasithinUnique.DoubleA3
