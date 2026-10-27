module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSL25

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

section Excl

variable {L : Subgroup G}

theorem card_alt3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide +kernel

theorem not_alt3_of_alt5 (h5 : IsAltType L 5) : ¬ IsAltType L 3 := by
  rintro h3
  obtain ⟨α₃, hα₃, hα₃k, -⟩ := h3
  obtain ⟨α₅, hα₅, hα₅k, -⟩ := h5
  have h1 := Subgroup.card_ker_mul_card_range α₃
  have h2 := Subgroup.card_ker_mul_card_range α₅
  rw [MonoidHom.range_eq_top.2 hα₃, Subgroup.card_top, card_alt3, hα₃k] at h1
  rw [MonoidHom.range_eq_top.2 hα₅, Subgroup.card_top, card_alt5, hα₅k] at h2
  have hpos : 0 < Nat.card ↥(CFSG.pCore 2 ↥L) := Nat.card_pos
  omega

theorem not_lin2_of_alt5 (hL : IsShort2 L) (h5 : IsAltType L 5) {n : ℕ} (hn : 1 < n) :
    ¬ IsLin2Type L n := by
  classical
  rintro ⟨F, hF, hFin, hcard, α₂, hα₂, hα₂k, β₂, hβ₂, hβ₂k, hβ₂e⟩
  have h5' := h5
  obtain ⟨α, hα, hαk, -⟩ := h5'
  obtain ⟨β₅, hβ₅⟩ := exists_beta hL h5 α hα hαk
  have hZ := blockZ_eq_bot_of_alt5 hL h5
  have hinj₂ : Function.Injective β₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₂k, hZ, Subgroup.bot_subgroupOf]
  obtain ⟨lam, hlam0, hlam1⟩ : ∃ lam : F, lam ≠ 0 ∧ lam ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have h2 := Finset.card_le_card hsub
    have h3 := Finset.card_le_two (a := (0 : F)) (b := 1)
    rw [Finset.card_univ, hcard] at h2
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  let e₂ : ↥(blockU L) ≃* Multiplicative (Fin 2 → F) := MulEquiv.ofBijective β₂ ⟨hinj₂, hβ₂⟩
  let Ω : ↥(blockU L) → ↥(blockU L) := fun u =>
    e₂.symm (Multiplicative.ofAdd (lam • Multiplicative.toAdd (e₂ u)))
  have hΩβ : ∀ u, Multiplicative.toAdd (β₂ (Ω u)) = lam • Multiplicative.toAdd (β₂ u) := by
    intro u
    have : β₂ (Ω u) = Multiplicative.ofAdd (lam • Multiplicative.toAdd (β₂ u)) :=
      e₂.apply_symm_apply _
    rw [this]; rfl
  have hΩmul : ∀ u u', Ω (u * u') = Ω u * Ω u' := by
    intro u u'
    apply hinj₂
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, hΩβ, hΩβ, hΩβ, map_mul, toAdd_mul, smul_add]
  have hΩinj : Function.Injective Ω := by
    intro u u' h
    apply hinj₂
    apply Multiplicative.toAdd.injective
    have := congrArg (fun v => Multiplicative.toAdd (β₂ v)) h
    simp only [hΩβ] at this
    exact smul_right_injective _ hlam0 this
  have hΩcomm : ∀ (ℓ : ↥L) (u u' : ↥(blockU L)), (u' : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ →
      (Ω u' : G) = (ℓ : G) * (Ω u : G) * (ℓ : G)⁻¹ := by
    intro ℓ u u' h
    have hmem : (ℓ : G) * (Ω u : G) * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ.2) _).mp (Ω u).2
    have h1 := hβ₂e ℓ u u' h
    have h2 := hβ₂e ℓ (Ω u) ⟨_, hmem⟩ rfl
    have h3 : Ω u' = ⟨_, hmem⟩ := by
      apply hinj₂
      apply Multiplicative.toAdd.injective
      rw [hΩβ, h1, h2, hΩβ, Matrix.mulVec_smul]
    exact congrArg Subtype.val h3
  let g : evenWeight 5 → evenWeight 5 := fun w =>
    Multiplicative.toAdd (β₅ (Ω (β₅.symm (Multiplicative.ofAdd w))))
  have hadd : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    show Multiplicative.toAdd (β₅ (Ω (β₅.symm (Multiplicative.ofAdd (x + y))))) = _
    rw [ofAdd_add, map_mul, hΩmul, map_mul, toAdd_mul]
  have hginj : Function.Injective g := by
    intro x y h
    have := β₅.injective (Multiplicative.toAdd.injective h)
    have h2 := hΩinj this
    have h3 := β₅.symm.injective h2
    exact Multiplicative.ofAdd.injective h3
  have hgcomm : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∀ w, g (vact σ w) = vact σ (g w) := by
    intro σ hσ w
    obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩
    have hαℓ : ((α ℓ : Alt5) : Perm (Fin 5)) = σ := by rw [hℓ]
    set u := β₅.symm (Multiplicative.ofAdd w) with hu
    set u' := β₅.symm (Multiplicative.ofAdd (vact σ w)) with hu'
    have hmem : (ℓ : G) * (u : G) * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ.2) _).mp u.2
    have hβu : Multiplicative.toAdd (β₅ u) = w := by simp [hu]
    have hrel : u' = ⟨_, hmem⟩ := by
      apply β₅.injective
      apply Multiplicative.toAdd.injective
      have := hβ₅ ℓ u ⟨_, hmem⟩ rfl
      rw [this, hβu, hαℓ]
      simp [hu']
    have hΩu' := hΩcomm ℓ u u' (by rw [hrel])
    have hrel2 : Ω u' = ⟨_, (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ.2) _).mp
        (Ω u).2⟩ := Subtype.ext hΩu'
    show Multiplicative.toAdd (β₅ (Ω u')) = vact σ (Multiplicative.toAdd (β₅ (Ω u)))
    rw [hrel2, hβ₅ ℓ (Ω u) _ rfl, hαℓ]
  have hrig := rigid g hadd hginj hgcomm
  have hfix : ∀ u : ↥(blockU L), Ω u = u := by
    intro u
    have h1 := hrig (Multiplicative.toAdd (β₅ u))
    have h2 : (g (Multiplicative.toAdd (β₅ u))) = Multiplicative.toAdd (β₅ (Ω u)) := by
      show Multiplicative.toAdd (β₅ (Ω (β₅.symm (Multiplicative.ofAdd (Multiplicative.toAdd
        (β₅ u)))))) = _
      simp
    rw [h2] at h1
    exact β₅.injective (Multiplicative.toAdd.injective h1)
  obtain ⟨u₀, hu₀⟩ := hβ₂ (Multiplicative.ofAdd (Pi.single 0 1 : Fin 2 → F))
  have h1 := hΩβ u₀
  rw [hfix u₀, hu₀] at h1
  have h2 := congrFun h1 0
  simp at h2
  exact hlam1 h2.symm

end Excl

namespace Mate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : Cfg T M H S L) (m : Mate S T M₀ x)
include C m

theorem exists_involution_over_z :
    ∃ ℓ : ↥L, ℓ * ℓ = 1 ∧ ((C.P.α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = zA := by
  have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (L : Set G) := (m.V_le_S C).trans C.hSN
  have hzE : zA ∈ Eset := (mem_Eset_iff _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hzV : zA ∈ C.P.im (conjR (blockU L) x) := by
    rw [m.im_V C]; exact (mem_Estd _).2 hzE
  obtain ⟨t, htV, htz⟩ := (C.P.mem_im_pf hVN).1 hzV
  have htS : t ∈ S := m.V_le_S C htV
  have ht2 : t * t = 1 := by
    have := V_sq (x := x) C htV
    rwa [pow_two] at this
  obtain ⟨ℓ₀, hℓ₀⟩ := C.P.hα ⟨zA, Equiv.Perm.mem_alternatingGroup.2 zA_sign⟩
  have hℓ₀N : (ℓ₀ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer ℓ₀.2
  have hpℓ₀ : C.P.pf (ℓ₀ : G) = zA := by
    rw [C.P.pf_eq hℓ₀N, C.P.hπα (ℓ₀ : G) ℓ₀.2, hℓ₀]
  have hyH : (ℓ₀ : G)⁻¹ * t ∈ H := mul_mem (inv_mem (C56.le_H C.hcs ℓ₀.2)) (C.hSH htS)
  have hyN : (ℓ₀ : G)⁻¹ * t ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem hℓ₀N) (C.hSN htS)
  have hypf : C.P.pf ((ℓ₀ : G)⁻¹ * t) = 1 := by
    rw [C.P.pf_mul (inv_mem hℓ₀N) (C.hSN htS), C.P.pf_inv hℓ₀N, hpℓ₀, htz, inv_mul_cancel]
  have hyQ : (ℓ₀ : G)⁻¹ * t ∈ pCoreOf 2 H := by
    rw [C.P.pf_eq hyN] at hypf
    have h2 := (C.P.hker ⟨_, hyN⟩).1 hypf
    rw [← C.hQ]
    refine ⟨hyH, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have := h2 u hu
    calc u * ((ℓ₀ : G)⁻¹ * t)
        = ((((ℓ₀ : G)⁻¹ * t) * u * ((ℓ₀ : G)⁻¹ * t)⁻¹)) * ((ℓ₀ : G)⁻¹ * t) := by rw [this]
      _ = ((ℓ₀ : G)⁻¹ * t) * u := by group
  obtain ⟨u, hu, d, hd, hyud⟩ := C.exists_UD hyQ
  have huL : u ∈ L := C1.blockQ_le L (C1.blockU_le_blockQ C.hL hu)
  refine ⟨ℓ₀ * ⟨u, huL⟩, ?_, ?_⟩
  · apply Subtype.ext
    show ((ℓ₀ : G) * u) * ((ℓ₀ : G) * u) = 1
    set ℓ : G := (ℓ₀ : G) * u with hℓdef
    have htd : t = ℓ * d := by
      calc t = (ℓ₀ : G) * ((ℓ₀ : G)⁻¹ * t) := by group
        _ = (ℓ₀ : G) * (u * d) := by rw [hyud]
        _ = ℓ * d := by rw [hℓdef]; group
    have hdc : d * ℓ = ℓ * d := blockD_comm C.hj hd (mul_mem ℓ₀.2 huL)
    have hd2 : d * d = 1 := by
      have := (m.D_elem C).2 d hd
      rwa [pow_two] at this
    calc ℓ * ℓ = ℓ * ℓ * (d * d) := by rw [hd2, mul_one]
      _ = ℓ * (ℓ * d) * d := by group
      _ = ℓ * (d * ℓ) * d := by rw [hdc]
      _ = (ℓ * d) * (ℓ * d) := by group
      _ = t * t := by rw [← htd]
      _ = 1 := ht2
  · have hu' : (⟨u, huL⟩ : ↥L) ∈ C.P.α.ker := by
      rw [C.P.hαk]
      exact (mem_pCore_iff_mem_blockQ _).2 (C1.blockU_le_blockQ C.hL hu)
    rw [map_mul, MonoidHom.mem_ker.1 hu', mul_one, hℓ₀]

theorem blockQ_eq_blockU : blockQ L = blockU L := by
  refine le_antisymm ?_ (C1.blockU_le_blockQ C.hL)
  obtain ⟨ℓ, hℓ, hαℓ⟩ := m.exists_involution_over_z C
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ C.hL).trans (C1.blockQ_le L)
  have hN : ((blockU L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr (C1.le_normalizer_blockU L)
  have hmem : ∀ q ∈ C.P.α.ker, (q : G) ∈ blockQ L := fun q hq => by
    rw [C.P.hαk] at hq
    exact (mem_pCore_iff_mem_blockQ q).1 hq
  have key := central_cover_trivial (Λ := ↥L) C.hL.1 C.P.α C.P.hα ((blockU L).subgroupOf L)
    (fun u hu => by
      rw [MonoidHom.mem_ker]
      have hu' : u ∈ C.P.α.ker := by
        rw [C.P.hαk]
        exact (mem_pCore_iff_mem_blockQ u).2
          (C1.blockU_le_blockQ C.hL (Subgroup.mem_subgroupOf.1 hu))
      exact hu')
    (fun q hq => by
      have hqQ : (q : G) ∈ pCoreOf 2 H := C56.blockQ_le_pCoreOf C.hcs C.hj (hmem q hq)
      apply Subtype.ext
      have := (m.Q_elem C).2 (q : G) hqQ
      simpa [pow_two] using this)
    (fun q hq g => Subgroup.mem_subgroupOf.2 (C1.commutator_mem_blockU (hmem q hq) g.2))
    ℓ hℓ hαℓ
  intro q hq
  have hqL : q ∈ L := C1.blockQ_le L hq
  have hk : (⟨q, hqL⟩ : ↥L) ∈ C.P.α.ker := by
    rw [C.P.hαk]
    exact (mem_pCore_iff_mem_blockQ _).2 hq
  exact Subgroup.mem_subgroupOf.1 (key hk)

end Mate

end CFSG.QuasithinUnique.AppC
