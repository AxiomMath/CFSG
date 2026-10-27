module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Final
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9K

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3 Equiv

@[expose] def sixG1 : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def sixG2 : Perm (Fin 6) := swap 0 1 * swap 1 5

theorem sixG1_mem : sixG1 ∈ alternatingGroup (Fin 6) :=
  Perm.mem_alternatingGroup.mpr (by decide +kernel)

theorem sixG2_mem : sixG2 ∈ alternatingGroup (Fin 6) :=
  Perm.mem_alternatingGroup.mpr (by decide +kernel)

theorem six_cent : ∀ σ : Perm (Fin 6), σ * sixG1 * σ⁻¹ = sixG1 → σ * sixG2 * σ⁻¹ = sixG2 →
    σ = 1 := by decide +kernel

theorem conjNormal_six_injective :
    Function.Injective (MulAut.conjNormal :
      Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))) := by
  rw [injective_iff_map_eq_one]
  intro σ h
  apply six_cent
  · have := congrArg (fun f : MulAut (alternatingGroup (Fin 6)) =>
      ((f ⟨sixG1, sixG1_mem⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6))) h
    simpa using this
  · have := congrArg (fun f : MulAut (alternatingGroup (Fin 6)) =>
      ((f ⟨sixG2, sixG2_mem⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6))) h
    simpa using this

@[expose] noncomputable def sixAut : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
  (MulAut.conjNormal : Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range

theorem sixAut_normal : sixAut.Normal := by
  have hfin : Finite (MulAut (alternatingGroup (Fin 6))) :=
    Finite.of_injective (fun f : MulAut (alternatingGroup (Fin 6)) =>
      (f : alternatingGroup (Fin 6) → alternatingGroup (Fin 6))) DFunLike.coe_injective
  have hcard : Nat.card sixAut = 720 := by
    unfold sixAut
    rw [← Nat.card_congr (MonoidHom.ofInjective conjNormal_six_injective).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hle :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
  have hmul := Subgroup.card_mul_index sixAut
  rw [hcard] at hmul
  have hpos : 0 < sixAut.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hidx : sixAut.index ≤ 2 := by omega
  rcases Nat.lt_or_ge sixAut.index 2 with h | h
  · have h1 : sixAut.index = 1 := by omega
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.normal_top
  · exact Subgroup.normal_of_index_eq_two (le_antisymm hidx h)

section Ind

variable {G : Type} [Group G] {K : Subgroup G}

@[expose] def indSix (e : ↥K ≃* alternatingGroup (Fin 6)) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ ∃ σ : Perm (Fin 6), InducesPerm e g σ}
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨ha1, σ₁, hσ₁⟩ := ha
    obtain ⟨hb1, σ₂, hσ₂⟩ := hb
    exact ⟨Subgroup.mul_mem _ ha1 hb1, σ₁ * σ₂, InducesPerm.mul' hσ₁ hσ₂ ha1⟩
  one_mem' := ⟨Subgroup.one_mem _, 1, fun k k' hk => by
    have : k' = k := Subtype.ext (by simpa using hk)
    rw [this]
    simp⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨ha1, σ, hσ⟩ := ha
    refine ⟨Subgroup.inv_mem _ ha1, σ⁻¹, fun k k' hk => ?_⟩
    have hk' : (k : G) = a⁻¹ * (k' : G) * a := by
      have : (k' : G) = a * (k : G) * a⁻¹ := by simpa using hk
      rw [this]
      group
    have := hσ k' k hk'
    rw [inv_inv]
    calc ((e k' : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        σ * (σ⁻¹ * ((e k' : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ) * σ⁻¹ := by group
      _ = σ * ((e k : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ⁻¹ := by rw [← this]

theorem indSix_conj (e : ↥K ≃* alternatingGroup (Fin 6)) {x g : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (hg : g ∈ indSix e) : x⁻¹ * g * x ∈ indSix e := by
  obtain ⟨hgN, σ, hσ⟩ := hg
  have hxg : x⁻¹ * g * x ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem_normalizer' hx) hgN) hx
  refine ⟨hxg, ?_⟩
  let ξ : MulAut (alternatingGroup (Fin 6)) := MulAut.congr e (conjAutK x hx)
  let c : MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal σ⁻¹
  have hcmem : c ∈ sixAut := ⟨σ⁻¹, rfl⟩
  have hmem : ξ * c * ξ⁻¹ ∈ sixAut := sixAut_normal.conj_mem c hcmem ξ
  obtain ⟨τ, hτ⟩ := hmem
  refine ⟨τ⁻¹, fun k k' hk => ?_⟩
  have hk₁ : x * (k : G) * x⁻¹ ∈ K := by
    have := conj_mem_of_normalizer (inv_mem_normalizer' hx) k
    simpa using this
  let k₁ : ↥K := ⟨x * (k : G) * x⁻¹, hk₁⟩
  let k₂ : ↥K := ⟨g⁻¹ * (k₁ : G) * g, conj_mem_of_normalizer hgN k₁⟩
  have hk' : k' = conjAutK x hx k₂ := by
    apply Subtype.ext
    have h1 : (k' : G) = (x⁻¹ * g * x)⁻¹ * (k : G) * (x⁻¹ * g * x) := hk
    rw [h1]
    show _ = x⁻¹ * (g⁻¹ * (x * (k : G) * x⁻¹) * g) * x
    group
  have hξinv : ξ⁻¹ (e k) = e k₁ := by
    show (MulAut.congr e (conjAutK x hx))⁻¹ (e k) = e k₁
    rw [← map_inv]
    show e ((conjAutK x hx)⁻¹ (e.symm (e k))) = e k₁
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hc : c (e k₁) = e k₂ := by
    have h2 := hσ k₁ k₂ rfl
    apply Subtype.ext
    rw [h2]
    simp [c]
  have hξ : ξ (e k₂) = e (conjAutK x hx k₂) := by
    show e (conjAutK x hx (e.symm (e k₂))) = _
    rw [MulEquiv.symm_apply_apply]
  have hτk : (MulAut.conjNormal τ : MulAut (alternatingGroup (Fin 6))) (e k) =
      (ξ * c * ξ⁻¹) (e k) := by rw [hτ]
  have : ((e k' : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      ((MulAut.conjNormal τ (e k) : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
    rw [hτk, hk']
    show _ = ((ξ (c (ξ⁻¹ (e k))) : alternatingGroup (Fin 6)) : Perm (Fin 6))
    rw [hξinv, hc, hξ]
  rw [this, MulAut.conjNormal_apply, inv_inv]

end Ind

namespace U9Data

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V : Subgroup G}
  (D : U9Data T M H S L z u A V)

include D

theorem U_eq_sup {v : G} (hvC : v ∈ blockU L ⊓ Subgroup.centralizer (A : Set G)) (hv1 : v ≠ 1)
    (hvu : v ≠ u) : blockU L = V ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := by
  set C : Subgroup G := blockU L ⊓ Subgroup.centralizer (A : Set G) with hCdef
  have hC4 : Nat.card ↥C = 4 := by
    have := D.s7.CU_card
    rwa [← D.A_eq] at this
  have huC : u ∈ C := ⟨D.s7.u_U, Subgroup.mem_centralizer_iff.mpr fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (D.A_le_Hu ha).2⟩
  have hv2 : v * v = 1 := by
    rw [← pow_two]
    exact D.U_sq v hvC.1
  have hvord : Nat.card (Subgroup.zpowers v) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((pow_two v).trans hv2) hv1
  have huord : Nat.card (Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((pow_two u).trans D.u_sq') D.u_ne_one
  have hcomm : Commute u v := D.U_comm u D.s7.u_U v hvC.1
  have hvC' : v ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left hcomm n).eq
  have hvnorm : Subgroup.zpowers v ≤
      Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hvC').trans (Subgroup.centralizer_le_normalizer _)
  have hmulW := C5.card_sup_mul_card_inf_of_le_normalizer hvnorm
  have hinf : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyu, hyv⟩
    rw [Subgroup.mem_bot]
    rcases (mem_zpowers_iff_of_sq_eq_one (by rw [pow_two]; exact D.u_sq')).mp hyu with h1 | h1
    · exact h1
    · rcases (mem_zpowers_iff_of_sq_eq_one (by rw [pow_two]; exact hv2)).mp hyv with h2 | h2
      · exact h2
      · exact absurd (h2.symm.trans h1) hvu
  have hWcard : Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) = 4 := by
    rw [sup_comm]
    have h := hmulW
    rw [inf_comm, hinf, Subgroup.card_bot, huord, hvord] at h
    omega
  have hWC : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ C :=
    sup_le (Subgroup.zpowers_le.mpr huC) (Subgroup.zpowers_le.mpr hvC)
  have hWeq : Subgroup.zpowers u ⊔ Subgroup.zpowers v = C :=
    Subgroup.eq_of_le_of_card_ge hWC (by rw [hC4, hWcard])
  obtain ⟨c, hcA, -, -, hcfp, -⟩ := D.hA.exists_c
  have hVC : V ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyV, hyC⟩
    rw [Subgroup.mem_bot]
    by_contra hy1
    apply hcfp y hyV hy1
    have := Subgroup.mem_centralizer_iff.mp hyC.2 c hcA
    calc c * y * c⁻¹ = (y * c) * c⁻¹ := by rw [this]
      _ = y := by group
  have hCnorm : C ≤ Subgroup.normalizer (V : Set G) := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact D.U_comm y (D.V_le hy) g hg.1
  have hmulVC := C5.card_sup_mul_card_inf_of_le_normalizer hCnorm
  have hVCcard : Nat.card ↥(V ⊔ C) = 16 := by
    rw [sup_comm]
    have h := hmulVC
    rw [inf_comm, hVC, Subgroup.card_bot, D.hA.card_U, hC4] at h
    omega
  have hsupU : V ⊔ C ≤ blockU L := sup_le D.V_le inf_le_left
  have hVCU : V ⊔ C = blockU L :=
    Subgroup.eq_of_le_of_card_ge hsupU (by rw [D.U_card, hVCcard])
  rw [← hVCU, ← hWeq]

theorem R_induces_perm {K : Subgroup G} (hK : K ≤ centralizerElem u)
    (hKnorm : centralizerElem u ≤ Subgroup.normalizer (K : Set G)) (hAK : A ≤ K)
    (e : ↥K ≃* alternatingGroup (Fin 6)) {v : G} {τ : Perm (Fin 6)}
    (hvC : v ∈ blockU L ⊓ Subgroup.centralizer (A : Set G)) (hv1 : v ≠ 1) (hvu : v ≠ u)
    (hvτ : InducesPerm e v τ) : ∀ r ∈ baum S, ∃ σ : Perm (Fin 6), InducesPerm e r σ := by
  have hvGu : v ∈ centralizerElem u :=
    Subgroup.mem_centralizer_singleton_iff.mpr (D.U_comm v hvC.1 u D.s7.u_U)
  have huGu : u ∈ centralizerElem u := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have huP : u ∈ indSix e := by
    refine ⟨hKnorm huGu, 1, fun k k' hk' => ?_⟩
    have hku : (k : G) * u = u * k := Subgroup.mem_centralizer_singleton_iff.mp (hK k.2)
    have : k' = k := Subtype.ext (by
      rw [hk']
      calc u⁻¹ * (k : G) * u = u⁻¹ * ((k : G) * u) := by group
        _ = u⁻¹ * (u * k) := by rw [hku]
        _ = k := by group)
    rw [this]
    simp
  have hvP : v ∈ indSix e := ⟨hKnorm hvGu, τ, hvτ⟩
  have hVP : V ≤ indSix e := fun y hy => by
    have hyK : y ∈ K := hAK (D.V_le_A hy)
    exact ⟨Subgroup.le_normalizer hyK, _, inducesPerm_of_mem e ⟨y, hyK⟩⟩
  have hU : blockU L ≤ indSix e := by
    rw [D.U_eq_sup hvC hv1 hvu]
    exact sup_le hVP (sup_le (Subgroup.zpowers_le.mpr huP) (Subgroup.zpowers_le.mpr hvP))
  obtain ⟨x, hxT, hxS, hxu⟩ := D.s7.x_exists
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hKnorm hxu
  have hUx : conjR (blockU L) x ≤ indSix e := by
    intro y hy
    rw [mem_conjR_iff] at hy
    have := indSix_conj e hxN (hU hy)
    simpa [mul_assoc] using this
  intro r hr
  rw [D.R_eq x hxT hxS] at hr
  exact ((sup_le hU hUx : blockU L ⊔ conjR (blockU L) x ≤ indSix e) hr).2

end U9Data

end CFSG.QuasithinUnique.A5
