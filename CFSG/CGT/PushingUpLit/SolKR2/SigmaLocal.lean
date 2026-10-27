module

public import CFSG.CGT.PushingUpLit.SolKR2.Setting
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI BenderCenterInput
  UnitaryTwoGenerationInput)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G] [Finite G]

@[expose] def SigmaCommIn (M V : Subgroup G) : Prop :=
  ∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → ∀ g h : G, conjSubgroup g V ≤ R →
    conjSubgroup h V ≤ R → ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a

section Certificates34

namespace SigmaCommIn

variable {M U : Subgroup G} (H : S3Hyp M U)
include H

theorem comm_of_le (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaCommIn M (omegaOneSub U)) {g : G} (hgM : conjSubgroup g U ≤ M) {h : G}
    (hhM : conjSubgroup h (omegaOneSub U) ≤ M) :
    ∀ a ∈ conjSubgroup h (omegaOneSub U),
      ∀ c ∈ conjSubgroup g (omegaOneSub U), a * c = c * a := by
  have hCc := Tim78.comm_conj H.comm g
  have hC2 : IsPGroup 2 (conjSubgroup g U) := H.two.map (MulAut.conj g).toMonoidHom
  have hCTI := isTI_conjSubgroup H.ti g
  rcases tim78_2_15 hCen hU H.fstar hgM hCc hC2 (fun k _ => hCTI k) with h1 | h2 | ⟨-, hW⟩
  · exact absurd h1 (H.omega_conj_ne g)
  · exact absurd h2 (H.not_isCyclic_conj g)
  · rw [omegaOneSub_conj H.comm] at hW
    set W := ⨆ (k : G) (_ : k ∈ M), conjSubgroup k (conjSubgroup g (omegaOneSub U))
      with hWdef
    have hMW : M ≤ Subgroup.normalizer (W : Set G) := by
      have e : W = ⨆ k : ↥M, conjSubgroup (k : G) (conjSubgroup g (omegaOneSub U)) := by
        rw [hWdef, iSup_subtype']
      rw [e]
      exact le_normalizer_iSup
    have hW2 : IsPGroup 2 W := fun w =>
      ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hW.2 w w.2)⟩
    have hA2 : IsPGroup 2 (conjSubgroup h (omegaOneSub U)) :=
      (H.two.to_le (omegaOneSub_le U)).map (MulAut.conj h).toMonoidHom
    have hR := IsPGroup.to_sup_of_normal_right' hA2 hW2 (le_trans hhM hMW)
    have hCW : conjSubgroup g (omegaOneSub U) ≤ W := by
      intro c hc
      refine Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem M.one_mem ?_)
      rw [conjSubgroup_one]
      exact hc
    have hgV : conjSubgroup g (omegaOneSub U) ≤ M :=
      le_trans (Subgroup.map_mono (omegaOneSub_le U)) hgM
    have hWM : W ≤ M := by
      refine iSup_le fun k => iSup_le fun hk => ?_
      intro z hz
      rw [mem_conjSubgroup] at hz
      rw [show z = k * (k⁻¹ * z * k) * k⁻¹ by group]
      exact M.mul_mem (M.mul_mem hk (hgV hz)) (M.inv_mem hk)
    exact hS _ (sup_le hhM hWM) hR h g le_sup_left (le_trans hCW le_sup_right)

theorem weaklyClosed (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaCommIn M (omegaOneSub U)) {g : G}
    (hg : conjSubgroup g U ≤ Subgroup.centralizer (U : Set G)) : conjSubgroup g U = U := by
  have hgM : conjSubgroup g U ≤ M := by
    rw [← H.normalizer_U_eq]
    exact le_trans hg (Subgroup.centralizer_le_normalizer (U : Set G))
  have h1M : conjSubgroup 1 U ≤ M := by
    rw [conjSubgroup_one]
    exact H.le
  have hmem := H.mem_of_comm (g := g) (fun h hh => comm_of_le H hCen hU hS hgM hh)
    (fun h hh a ha c hc => comm_of_le H hCen hU hS h1M hh a ha c (by
      rw [conjSubgroup_one]; exact hc))
  exact conjSubgroup_eq_self_iff.mpr (H.normal hmem)

theorem stronglyClosed (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaCommIn M (omegaOneSub U)) {b g : G} (hb : b ∈ U)
    (hbg : g * b * g⁻¹ ∈ Subgroup.centralizer (U : Set G)) : g * b * g⁻¹ ∈ U := by
  by_cases hb1 : b = 1
  · rw [hb1, mul_one, mul_inv_cancel]
    exact U.one_mem
  have hb' : g * b * g⁻¹ ∈ conjSubgroup g U := by
    rw [mem_conjSubgroup, show g⁻¹ * (g * b * g⁻¹) * g = b by group]
    exact hb
  have hb'1 : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hCTI := isTI_conjSubgroup H.ti g
  have hle : conjSubgroup g⁻¹ (conjSubgroup g U) ≤
      Subgroup.normalizer (conjSubgroup g U : Set G) := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    intro x hx
    exact Tim77.mem_normalizer_of_commute_of_isTI hCTI hb' hb'1
      (Subgroup.mem_centralizer_iff.mp hbg x hx)
  have hC1 : conjSubgroup g U ≠ ⊥ := fun h => hb'1 (by
    rw [h, Subgroup.mem_bot] at hb'
    exact hb')
  have hcomm := commute_of_le_normalizer (Tim78.comm_conj H.comm g)
    (H.two.map (MulAut.conj g).toMonoidHom) hC1 hCTI hle
  have hCU : conjSubgroup g U ≤ Subgroup.centralizer (U : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => (hcomm c hc u (by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
      exact hu)).symm
  rw [← weaklyClosed H hCen hU hS hCU]
  exact hb'

theorem comm_mem_of_invol (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaCommIn M (omegaOneSub U)) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSM : S ≤ M) (hQS : inSubgroup (pCore 2) M ≤ S) {h : G}
    (hA₀S : conjSubgroup h (omegaOneSub U) ≤ S)
    (hA₀V : conjSubgroup h (omegaOneSub U) ≠ omegaOneSub U) {t : G}
    (htP : t ∈ inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (U : Set G)) (ht2 : t * t = 1) :
    ∀ a ∈ conjSubgroup h (omegaOneSub U),
      a * t * a⁻¹ * t⁻¹ ∈ omegaOneSub U := by
  classical
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hroot := H.root hCen hU
  have hVTI := hroot.1
  have hVe : ∀ v ∈ omegaOneSub U, v * v = 1 := fun v hv =>
    ((mem_omegaOneSub_iff H.comm).mp hv).2
  have hsc := fun {b g : G} (hb : b ∈ U) (hbg : g * b * g⁻¹ ∈ Subgroup.centralizer (U : Set G)) =>
    stronglyClosed H hCen hU hS hb hbg
  have hVC : ∀ k w : G, w ∈ conjSubgroup k (omegaOneSub U) →
      w ∈ Subgroup.centralizer (U : Set G) → w ∈ omegaOneSub U := by
    intro k w hw hwC
    have hw' : k⁻¹ * w * k ∈ omegaOneSub U := mem_conjSubgroup.mp hw
    have h1 := hsc (omegaOneSub_le U hw') (g := k)
      (by rw [show k * (k⁻¹ * w * k) * k⁻¹ = w by group]; exact hwC)
    rw [show k * (k⁻¹ * w * k) * k⁻¹ = w by group] at h1
    exact (mem_omegaOneSub_iff H.comm).mpr ⟨h1, mul_self_of_mem_conj hVe hw⟩
  obtain ⟨htQ, htC⟩ := Subgroup.mem_inf.mp htP
  have htU : ∀ u ∈ U, t * u = u * t := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp htC u hu).symm
  have htM : t ∈ M := hQM htQ
  have htS : t ∈ S := hQS htQ
  have hcommP : ∀ m ∈ M, m * t * m⁻¹ * t⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro m hm
    have hmP : m ∈ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
      mem_normalizer_centralizer (H.normal hm)
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hmP t).mp htC)
      (Subgroup.inv_mem _ htC)
  have hVA : omegaOneSub U ⊓ conjSubgroup h (omegaOneSub U) = ⊥ :=
    inf_conjSubgroup_eq_bot_of_isTI hVTI hA₀V
  by_cases hcase : ∀ a ∈ conjSubgroup h (omegaOneSub U), a * t = t * a
  · intro a ha
    rw [hcase a ha, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  simp only [not_forall] at hcase
  obtain ⟨a₀, ha₀, hat⟩ := hcase
  have hat' : a₀ * t * a₀⁻¹ * t⁻¹ ≠ 1 := fun h1 => hat (by
    calc a₀ * t = (a₀ * t * a₀⁻¹ * t⁻¹) * (t * a₀) := by group
      _ = t * a₀ := by rw [h1, one_mul])
  set A := conjSubgroup h U with hAdef
  have hA₀ : omegaOneSub A = conjSubgroup h (omegaOneSub U) :=
    omegaOneSub_conj H.comm h
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := Tim78.comm_conj H.comm h
  have hA2 : IsPGroup 2 A := H.two.map (MulAut.conj h).toMonoidHom
  have hATI : IsTI A := isTI_conjSubgroup H.ti h
  have hAexp : ∀ z ∈ A, z ^ 4 = 1 := by
    intro z hz
    have h4 := H.exp _ (mem_conjSubgroup.mp hz)
    rw [show (h⁻¹ * z * h) ^ 4 = h⁻¹ * z ^ 4 * h by
      simpa using conj_pow (a := h⁻¹) (b := z) (i := 4)] at h4
    calc z ^ 4 = h * (h⁻¹ * z ^ 4 * h) * h⁻¹ := by group
      _ = 1 := by rw [h4]; group
  have hAne : ∃ z ∈ A, z ^ 2 ≠ 1 := by
    obtain ⟨u, hu, hu2⟩ := H.exp_ne
    refine ⟨h * u * h⁻¹, ?_, fun h' => hu2 ?_⟩
    · rw [mem_conjSubgroup, show h⁻¹ * (h * u * h⁻¹) * h = u by group]
      exact hu
    · rw [conj_pow] at h'
      calc u ^ 2 = h⁻¹ * (h * u ^ 2 * h⁻¹) * h := by group
        _ = 1 := by rw [h']; group
  have hA₀tS : conjSubgroup t (conjSubgroup h (omegaOneSub U)) ≤ S := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    rw [show z = t * (t⁻¹ * z * t) * t⁻¹ by group]
    exact S.mul_mem (S.mul_mem htS (hA₀S hz)) (S.inv_mem htS)
  have hcommAt : ∀ a ∈ conjSubgroup h (omegaOneSub U),
      ∀ b ∈ conjSubgroup t (conjSubgroup h (omegaOneSub U)), a * b = b * a := by
    have := hS S hSM hS2 h (t * h) hA₀S (by rw [conjSubgroup_mul]; exact hA₀tS)
    rwa [conjSubgroup_mul] at this
  have hA₀ne : conjSubgroup h (omegaOneSub U) ≠ ⊥ := by
    intro hbot
    apply H.omega_ne_bot
    have := card_conjSubgroup h (omegaOneSub U)
    rw [hbot, Subgroup.card_bot] at this
    exact Subgroup.eq_bot_of_card_eq _ this.symm
  have hsetup : Setup210 A (conjSubgroup t A) :=
    { comm := hAc
      two := hA2
      exp_ne := hAne
      ti := hATI
      conj := ⟨t, rfl⟩
      ne_bot := by
        intro hbot
        apply hA₀ne
        rw [eq_bot_iff, ← hbot]
        intro a ha
        refine Subgroup.mem_inf.mpr ⟨by
          rw [hAdef, mem_conjSubgroup]
          exact omegaOneSub_le U (mem_conjSubgroup.mp ha), ?_⟩
        have hL1 : omegaOneSub (conjSubgroup t A) ≠ ⊥ := by
          rw [omegaOneSub_conj hAc, hA₀]
          intro hb
          apply hA₀ne
          have := card_conjSubgroup t (conjSubgroup h (omegaOneSub U))
          rw [hb, Subgroup.card_bot] at this
          exact Subgroup.eq_bot_of_card_eq _ this.symm
        rw [← mem_normalizer_omega_iff (Tim78.comm_conj hAc t) (isTI_conjSubgroup hATI t) hL1]
        refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
          fun b hb => (hcommAt a ha b ?_).symm)
        rw [omegaOneSub_conj hAc, hA₀] at hb
        exact hb }
  by_cases hAA : ∀ a ∈ A, ∀ b ∈ conjSubgroup t A, a * b = b * a
  ·
    exfalso
    have hc : conjSubgroup (h⁻¹ * t * h) U ≤ Subgroup.centralizer (U : Set G) := by
      intro z hz
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      have hz' : h * z * h⁻¹ ∈ conjSubgroup t A := by
        rw [hAdef, ← conjSubgroup_mul, mem_conjSubgroup,
          show (t * h)⁻¹ * (h * z * h⁻¹) * (t * h) =
            (h⁻¹ * t * h)⁻¹ * z * (h⁻¹ * t * h) by group]
        exact mem_conjSubgroup.mp hz
      have hu' : h * u * h⁻¹ ∈ A := by
        rw [hAdef, mem_conjSubgroup, show h⁻¹ * (h * u * h⁻¹) * h = u by group]
        exact hu
      have h1 := hAA _ hu' _ hz'
      calc u * z = h⁻¹ * ((h * u * h⁻¹) * (h * z * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * z * h⁻¹) * (h * u * h⁻¹)) * h := by rw [h1]
        _ = z * u := by group
    have hw := weaklyClosed H hCen hU hS hc
    have htA : conjSubgroup t A = A := by
      rw [hAdef, ← conjSubgroup_mul, show t * h = h * (h⁻¹ * t * h) by group, conjSubgroup_mul,
        hw]
    have htA₀ : ∀ a ∈ conjSubgroup h (omegaOneSub U),
        t * a * t⁻¹ ∈ conjSubgroup h (omegaOneSub U) := by
      intro a ha
      rw [← hA₀] at ha ⊢
      rw [← htA, omegaOneSub_conj hAc, mem_conjSubgroup,
        show t⁻¹ * (t * a * t⁻¹) * t = a by group]
      exact ha
    have h1 : a₀ * t * a₀⁻¹ * t⁻¹ ∈ conjSubgroup h (omegaOneSub U) := by
      rw [show a₀ * t * a₀⁻¹ * t⁻¹ = a₀ * (t * a₀⁻¹ * t⁻¹) by group]
      exact Subgroup.mul_mem _ ha₀ (htA₀ _ (Subgroup.inv_mem _ ha₀))
    have h3 := hVC h _ h1 (hcommP a₀ (hSM (hA₀S ha₀)))
    have : a₀ * t * a₀⁻¹ * t⁻¹ ∈ omegaOneSub U ⊓
        conjSubgroup h (omegaOneSub U) := Subgroup.mem_inf.mpr ⟨h3, h1⟩
    rw [hVA, Subgroup.mem_bot] at this
    exact hat' this
  have Pr : NCPair A (conjSubgroup t A) := ⟨hsetup, hAexp, hAA⟩
  have htX : t ∈ Subgroup.normalizer ((A ⊔ conjSubgroup t A : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_swap ht2 A
  obtain ⟨x₀, hx₀, he⟩ := Pr.exists_conj hCen hU
  obtain ⟨x, hx, hxD⟩ := Pr.exists_fixed hCen hU ht2 htX ⟨x₀, hx₀, he⟩
  have hD₀ : omegaOneSub (conjSubgroup x A) =
      conjSubgroup (x * h) (omegaOneSub U) := by
    rw [omegaOneSub_conj hAc, hA₀, conjSubgroup_mul]
  have hNS : omegaOneSub A ⊔ omegaOneSub (conjSubgroup t A) ≤ S := by
    rw [omegaOneSub_conj hAc, hA₀]
    exact sup_le hA₀S hA₀tS
  have hD₀M : omegaOneSub (conjSubgroup x A) ≤ M :=
    le_trans (Pr.omega_conj_le_N hCen hU hx) (le_trans hNS hSM)
  have htD₀ : ∀ d ∈ omegaOneSub (conjSubgroup x A),
      t * d * t⁻¹ ∈ omegaOneSub (conjSubgroup x A) := by
    intro d hd
    rw [← hxD, omegaOneSub_conj (Tim78.comm_conj hAc x), mem_conjSubgroup,
      show t⁻¹ * (t * d * t⁻¹) * t = d by group]
    exact hd
  have hD₀t : ∀ d ∈ omegaOneSub (conjSubgroup x A), t * d = d * t := by
    intro d hd
    have hw1 : d * t * d⁻¹ * t⁻¹ ∈ omegaOneSub (conjSubgroup x A) := by
      rw [show d * t * d⁻¹ * t⁻¹ = d * (t * d⁻¹ * t⁻¹) by group]
      exact Subgroup.mul_mem _ hd (htD₀ _ (Subgroup.inv_mem _ hd))
    have hw3 := hVC (x * h) _ (by rw [← hD₀]; exact hw1) (hcommP d (hD₀M hd))
    by_cases hDV : conjSubgroup (x * h) (omegaOneSub U) = omegaOneSub U
    · rw [hD₀, hDV] at hd
      exact htU d (omegaOneSub_le U hd)
    · have hVD := inf_conjSubgroup_eq_bot_of_isTI hVTI hDV
      have : d * t * d⁻¹ * t⁻¹ ∈ omegaOneSub U ⊓
          conjSubgroup (x * h) (omegaOneSub U) :=
        Subgroup.mem_inf.mpr ⟨hw3, by rw [← hD₀]; exact hw1⟩
      rw [hVD, Subgroup.mem_bot] at this
      calc t * d = (d * t * d⁻¹ * t⁻¹)⁻¹ * (d * t) := by group
        _ = d * t := by rw [this, inv_one, one_mul]
  have hcomm_a : ∀ a ∈ conjSubgroup h (omegaOneSub U),
      a * t * a⁻¹ * t⁻¹ ∈ omegaOneSub (conjSubgroup x A) := by
    intro a ha
    have haN : a ∈ omegaOneSub A ⊔ omegaOneSub (conjSubgroup t A) :=
      Subgroup.mem_sup_left (by rw [hA₀]; exact ha)
    have h1 := Pr.commutator_mem_omega_of_swap' hCen hU ht2 rfl hx hD₀t haN
    have := (omegaOneSub (conjSubgroup x A)).inv_mem h1
    rwa [show (t * a * t⁻¹ * a⁻¹)⁻¹ = a * t * a⁻¹ * t⁻¹ by group] at this
  have hDV : conjSubgroup (x * h) (omegaOneSub U) = omegaOneSub U := by
    by_contra hne
    have hVD := inf_conjSubgroup_eq_bot_of_isTI hVTI hne
    have h1 := hcomm_a a₀ ha₀
    rw [hD₀] at h1
    have h3 := hVC (x * h) _ h1 (hcommP a₀ (hSM (hA₀S ha₀)))
    have : a₀ * t * a₀⁻¹ * t⁻¹ ∈ omegaOneSub U ⊓
        conjSubgroup (x * h) (omegaOneSub U) := Subgroup.mem_inf.mpr ⟨h3, h1⟩
    rw [hVD, Subgroup.mem_bot] at this
    exact hat' this
  intro a ha
  have := hcomm_a a ha
  rwa [hD₀, hDV] at this

theorem le_Q_of_le (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaCommIn M (omegaOneSub U)) {h : G}
    (hhM : conjSubgroup h (omegaOneSub U) ≤ M) :
    conjSubgroup h (omegaOneSub U) ≤ inSubgroup (pCore 2) M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hUQ : U ≤ inSubgroup (pCore 2) M := le_inSubgroup_pCore H.le H.normal H.two
  have hVQ : omegaOneSub U ≤ inSubgroup (pCore 2) M :=
    le_trans (omegaOneSub_le U) hUQ
  by_cases hV : conjSubgroup h (omegaOneSub U) = omegaOneSub U
  · rw [hV]
    exact hVQ
  have hroot := H.root hCen hU
  have hVe : ∀ v ∈ omegaOneSub U, v * v = 1 := fun v hv =>
    ((mem_omegaOneSub_iff H.comm).mp hv).2
  have hA₀2 : IsPGroup 2 (conjSubgroup h (omegaOneSub U)) :=
    (H.two.to_le (omegaOneSub_le U)).map (MulAut.conj h).toMonoidHom
  obtain ⟨P₀, hP₀⟩ := (hA₀2.comap_of_injective M.subtype
    M.subtype_injective).exists_le_sylow
  set S := (P₀ : Subgroup ↥M).map M.subtype with hSdef
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := P₀.isPGroup'.map M.subtype
  have hA₀S : conjSubgroup h (omegaOneSub U) ≤ S := fun z hz =>
    ⟨⟨z, hhM hz⟩, hP₀ hz, rfl⟩
  have hQS : inSubgroup (pCore 2) M ≤ S := by
    have hn : ((inSubgroup (pCore 2) M).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMQ
    have hp : IsPGroup 2 ((inSubgroup (pCore 2) M).subgroupOf M) :=
      hQ2.comap_of_injective _ Subtype.val_injective
    have hle := IsPGroup.le_sylow_of_normal hp P₀
    intro z hz
    exact ⟨⟨z, hQM hz⟩, hle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  set P := inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (U : Set G) with hPdef
  have hPQ : P ≤ inSubgroup (pCore 2) M := inf_le_left
  have hP2 : IsPGroup 2 P := hQ2.to_le hPQ
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := fun m hm =>
    mem_normalizer_inf (hMQ hm) (mem_normalizer_centralizer (H.normal hm))
  have hPV : ∀ p ∈ P, ∀ v ∈ omegaOneSub U, p * v = v * p := fun p hp v hv =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hp).2 v
      (omegaOneSub_le U hv)).symm
  have hVP : omegaOneSub U ≤ P := fun v hv =>
    Subgroup.mem_inf.mpr ⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      H.comm u hu v (omegaOneSub_le U hv)⟩
  set P₁ := Subgroup.closure {t | t ∈ P ∧ t * t = 1} with hP₁def
  have hP₁P : P₁ ≤ P := (Subgroup.closure_le _).mpr fun t ht => ht.1
  have hconjP₁ : ∀ m ∈ M, ∀ x ∈ P₁, m * x * m⁻¹ ∈ P₁ := by
    intro m hm x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht =>
        refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp (hMP hm) t).mp ht.1, ?_⟩
        calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
          _ = 1 := by rw [ht.2]; group
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [show m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) by group]
        exact P₁.mul_mem ihx ihy
    | inv x hx ihx =>
        rw [show m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ by group]
        exact P₁.inv_mem ihx
  have hconjV : ∀ m ∈ M, ∀ v ∈ omegaOneSub U, m * v * m⁻¹ ∈ omegaOneSub U :=
    fun m hm v hv => (Subgroup.mem_normalizer_iff.mp (H.le_normalizer_omega hm) v).mp hv
  have hA₀V : ∀ a ∈ conjSubgroup h (omegaOneSub U), ∀ v ∈ omegaOneSub U,
      a * v = v * a := by
    have hc := commute_of_isRootTypeTI hroot (g := h) (h := 1) (fun hbot => by
      have hA₀ne : conjSubgroup h (omegaOneSub U) ≠ ⊥ := by
        intro hb
        apply H.omega_ne_bot
        have := card_conjSubgroup h (omegaOneSub U)
        rw [hb, Subgroup.card_bot] at this
        exact Subgroup.eq_bot_of_card_eq _ this.symm
      apply hA₀ne
      rw [eq_bot_iff, ← hbot]
      intro a ha
      refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
      rw [conjSubgroup_one]
      exact H.le_normalizer_omega (hhM ha))
    intro a ha v hv
    exact hc a ha v (by rw [conjSubgroup_one]; exact hv)
  have hC3 : ∀ a ∈ conjSubgroup h (omegaOneSub U), ∀ x ∈ P₁,
      a * x * a⁻¹ * x⁻¹ ∈ omegaOneSub U := by
    intro a ha x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht => exact comm_mem_of_invol H hCen hU hS hS2 hSM hQS hA₀S hV ht.1 ht.2 a ha
    | one => simp
    | mul x y hx hy ihx ihy =>
        have hxy : x * (a * y * a⁻¹ * y⁻¹) * x⁻¹ = a * y * a⁻¹ * y⁻¹ := by
          rw [hPV x (hP₁P hx) _ ihy]
          group
        rw [show a * (x * y) * a⁻¹ * (x * y)⁻¹ =
          (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) by group, hxy]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
        have hxx : x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x = (a * x * a⁻¹ * x⁻¹)⁻¹ := by
          have h1 := hPV x (hP₁P hx) _ (Subgroup.inv_mem _ ihx)
          calc x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x =
              x⁻¹ * ((a * x * a⁻¹ * x⁻¹)⁻¹ * x) := by group
            _ = x⁻¹ * (x * (a * x * a⁻¹ * x⁻¹)⁻¹) := by rw [h1]
            _ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
        rw [show a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x by group, hxx]
        exact Subgroup.inv_mem _ ihx
  have hC4 : ∀ a ∈ conjSubgroup h (omegaOneSub U), ∀ p ∈ P,
      a * p * a⁻¹ * p⁻¹ ∈ P₁ := by
    intro a ha p hp
    apply Subgroup.subset_closure
    have haM := hhM ha
    refine ⟨Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hMP haM) p).mp hp)
      (Subgroup.inv_mem _ hp), ?_⟩
    have hpS : p ∈ S := hQS (hPQ hp)
    have hb : p * a * p⁻¹ ∈ conjSubgroup (p * h) (omegaOneSub U) := by
      rw [conjSubgroup_mul, mem_conjSubgroup, show p⁻¹ * (p * a * p⁻¹) * p = a by group]
      exact ha
    have hbS : conjSubgroup (p * h) (omegaOneSub U) ≤ S := by
      intro z hz
      rw [conjSubgroup_mul, mem_conjSubgroup] at hz
      rw [show z = p * (p⁻¹ * z * p) * p⁻¹ by group]
      exact S.mul_mem (S.mul_mem hpS (hA₀S hz)) (S.inv_mem hpS)
    have hab := hS S hSM hS2 h (p * h) hA₀S hbS a ha _ hb
    have haa := mul_self_of_mem_conj hVe ha
    have hbb := mul_self_of_mem_conj hVe hb
    have hbi : (p * a * p⁻¹)⁻¹ = p * a * p⁻¹ := inv_eq_of_mul_eq_one_right hbb
    rw [show a * p * a⁻¹ * p⁻¹ = a * (p * a * p⁻¹)⁻¹ by group, hbi]
    calc a * (p * a * p⁻¹) * (a * (p * a * p⁻¹)) = a * ((p * a * p⁻¹) * a) * (p * a * p⁻¹) := by
          group
      _ = a * (a * (p * a * p⁻¹)) * (p * a * p⁻¹) := by rw [← hab]
      _ = (a * a) * ((p * a * p⁻¹) * (p * a * p⁻¹)) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  let K : Subgroup G :=
    { carrier := {x | x ∈ M ∧ (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ P₁) ∧
        (∀ p ∈ P₁, x * p * x⁻¹ * p⁻¹ ∈ omegaOneSub U) ∧
        ∀ v ∈ omegaOneSub U, x * v = v * x}
      one_mem' := ⟨M.one_mem, fun p _ => by simp, fun p _ => by simp, fun v _ => by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨M.mul_mem hx.1 hy.1, fun p hp => by
          rw [show x * y * p * (x * y)⁻¹ * p⁻¹ =
            (x * (y * p * y⁻¹ * p⁻¹) * x⁻¹) * (x * p * x⁻¹ * p⁻¹) by group]
          exact P₁.mul_mem (hconjP₁ x hx.1 _ (hy.2.1 p hp)) (hx.2.1 p hp), fun p hp => by
          rw [show x * y * p * (x * y)⁻¹ * p⁻¹ =
            (x * (y * p * y⁻¹ * p⁻¹) * x⁻¹) * (x * p * x⁻¹ * p⁻¹) by group]
          exact Subgroup.mul_mem _ (hconjV x hx.1 _ (hy.2.2.1 p hp)) (hx.2.2.1 p hp),
          fun v hv => by
          calc x * y * v = x * (y * v) := by group
            _ = x * (v * y) := by rw [hy.2.2.2 v hv]
            _ = (x * v) * y := by group
            _ = (v * x) * y := by rw [hx.2.2.2 v hv]
            _ = v * (x * y) := by group⟩
      inv_mem' := fun {x} hx => ⟨M.inv_mem hx.1, fun p hp => by
          rw [show x⁻¹ * p * x⁻¹⁻¹ * p⁻¹ = x⁻¹ * (x * p * x⁻¹ * p⁻¹)⁻¹ * x⁻¹⁻¹ by group]
          exact hconjP₁ _ (M.inv_mem hx.1) _ (P₁.inv_mem (hx.2.1 p hp)), fun p hp => by
          rw [show x⁻¹ * p * x⁻¹⁻¹ * p⁻¹ = x⁻¹ * (x * p * x⁻¹ * p⁻¹)⁻¹ * x⁻¹⁻¹ by group]
          exact hconjV _ (M.inv_mem hx.1) _ (Subgroup.inv_mem _ (hx.2.2.1 p hp)),
          fun v hv => by
          have h1 := hx.2.2.2 v hv
          calc x⁻¹ * v = x⁻¹ * (v * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * v) * x⁻¹ := by rw [h1]
            _ = v * x⁻¹ := by group⟩ }
  have hA₀K : ∀ m : ↥M, conjSubgroup (m : G) (conjSubgroup h (omegaOneSub U)) ≤ K := by
    intro m z hz
    rw [mem_conjSubgroup] at hz
    set a := (m : G)⁻¹ * z * m with ha_def
    have hz' : z = (m : G) * a * (m : G)⁻¹ := by rw [ha_def]; group
    have hmi : (m : G)⁻¹ ∈ M := M.inv_mem m.2
    refine ⟨?_, fun p hp => ?_, fun p hp => ?_, fun v hv => ?_⟩
    · rw [hz']
      exact M.mul_mem (M.mul_mem m.2 (hhM hz)) hmi
    · have hp' : (m : G)⁻¹ * p * (m : G)⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hMP hmi) p).mp hp
      have h1 := hconjP₁ _ m.2 _ (hC4 a hz _ hp')
      rwa [show (m : G) * (a * ((m : G)⁻¹ * p * (m : G)⁻¹⁻¹) * a⁻¹ *
        ((m : G)⁻¹ * p * (m : G)⁻¹⁻¹)⁻¹) * (m : G)⁻¹ = z * p * z⁻¹ * p⁻¹ by rw [hz']; group]
        at h1
    · have hp' : (m : G)⁻¹ * p * (m : G)⁻¹⁻¹ ∈ P₁ := hconjP₁ _ hmi _ hp
      have h1 := hconjV _ m.2 _ (hC3 a hz _ hp')
      rwa [show (m : G) * (a * ((m : G)⁻¹ * p * (m : G)⁻¹⁻¹) * a⁻¹ *
        ((m : G)⁻¹ * p * (m : G)⁻¹⁻¹)⁻¹) * (m : G)⁻¹ = z * p * z⁻¹ * p⁻¹ by rw [hz']; group]
        at h1
    · have hv' : (m : G)⁻¹ * v * (m : G)⁻¹⁻¹ ∈ omegaOneSub U := hconjV _ hmi _ hv
      have h1 := hA₀V a hz _ hv'
      rw [hz']
      calc (m : G) * a * (m : G)⁻¹ * v =
          (m : G) * (a * ((m : G)⁻¹ * v * (m : G)⁻¹⁻¹)) * (m : G)⁻¹ := by group
        _ = (m : G) * (((m : G)⁻¹ * v * (m : G)⁻¹⁻¹) * a) * (m : G)⁻¹ := by rw [h1]
        _ = v * ((m : G) * a * (m : G)⁻¹) := by group
  set L := ⨆ m : ↥M, conjSubgroup (m : G) (conjSubgroup h (omegaOneSub U)) with hLdef
  have hLK : L ≤ K := iSup_le hA₀K
  have hLM : L ≤ M := fun z hz => (hLK hz).1
  have hML : M ≤ Subgroup.normalizer (L : Set G) := le_normalizer_iSup
  have hodd : ∀ y ∈ K, Odd (orderOf y) → ∀ p ∈ P, y * p = p * y := by
    intro y hy hyo
    have hy1 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
    have hstep1 : ∀ x ∈ P₁, y * x = x * y := by
      intro x hx
      have hc := hy.2.2.1 x hx
      have hd : x⁻¹ * (y * x * y⁻¹) = y * x * y⁻¹ * x⁻¹ := by
        have h1 := hPV x (hP₁P hx) _ hc
        calc x⁻¹ * (y * x * y⁻¹) = x⁻¹ * ((y * x * y⁻¹ * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (y * x * y⁻¹ * x⁻¹)) := by rw [h1]
          _ = y * x * y⁻¹ * x⁻¹ := by group
      have hd1 := eq_one_of_odd_conj (n := 1) hyo hy1
        (show y * x * y⁻¹ = x * (x⁻¹ * (y * x * y⁻¹)) by group)
        (by rw [hd]; exact hy.2.2.2 _ hc)
        (by rw [hd, pow_one, sq]; exact hVe _ hc)
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * (x⁻¹ * (y * x * y⁻¹)) * y := by group
        _ = x * y := by rw [hd1, mul_one]
    intro p hp
    have hc := hy.2.1 p hp
    have hdP₁ : p⁻¹ * (y * p * y⁻¹) ∈ P₁ := by
      have := hconjP₁ _ (hPQ.trans hQM (P.inv_mem hp)) _ hc
      rwa [show p⁻¹ * (y * p * y⁻¹ * p⁻¹) * p⁻¹⁻¹ = p⁻¹ * (y * p * y⁻¹) by group] at this
    obtain ⟨n, hn⟩ := hP2 ⟨_, hP₁P hdP₁⟩
    have hd1 := eq_one_of_odd_conj (n := n) hyo hy1
      (show y * p * y⁻¹ = p * (p⁻¹ * (y * p * y⁻¹)) by group) (hstep1 _ hdP₁)
      (by simpa using congrArg Subtype.val hn)
    calc y * p = (y * p * y⁻¹) * y := by group
      _ = p * (p⁻¹ * (y * p * y⁻¹)) * y := by group
      _ = p * y := by rw [hd1, mul_one]
  have hα := tim78_2_9_alpha H.fstar H.le H.normal
    ⟨⟨fun a b => Subtype.ext (H.comm _ a.2 _ b.2)⟩⟩ hPdef
  have hL2 : IsPGroup 2 L := by
    intro z
    obtain ⟨a, ha, -⟩ := exists_odd_orderOf_pow (z : G)
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    have hyL : (z : G) ^ 2 ^ a ∈ L := L.pow_mem z.2 _
    have hyK := hLK hyL
    have hyC : (z : G) ^ 2 ^ a ∈ M ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hyK.1, Subgroup.mem_centralizer_iff.mpr fun p hp => (hodd _ hyK ha p hp).symm⟩
    rw [hα] at hyC
    exact eq_one_of_odd_of_isPGroup hP2 hyC.1 ha
  have hLQ : L ≤ inSubgroup (pCore 2) M := le_inSubgroup_pCore hLM hML hL2
  intro z hz
  refine hLQ (Subgroup.mem_iSup_of_mem ⟨1, M.one_mem⟩ ?_)
  rw [conjSubgroup_one]
  exact hz

theorem weaklyClosed_omega (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaCommIn M (omegaOneSub U)) :
    ∀ g : G, conjSubgroup g (omegaOneSub U) ≤ M →
      conjSubgroup g (omegaOneSub U) = omegaOneSub U := by
  intro g hg
  obtain ⟨hQ2, hQM, -⟩ := inSubgroup_pCore_two M
  have hgQ := le_Q_of_le H hCen hU hS hg
  have hVQ : conjSubgroup 1 (omegaOneSub U) ≤ inSubgroup (pCore 2) M := by
    rw [conjSubgroup_one]
    exact le_trans (omegaOneSub_le U) (le_inSubgroup_pCore H.le H.normal H.two)
  have hmem := H.mem_of_comm (g := g)
    (fun k hk => hS _ hQM hQ2 k g (le_Q_of_le H hCen hU hS hk) hgQ)
    (fun k hk a ha c hc => hS _ hQM hQ2 k 1 (le_Q_of_le H hCen hU hS hk) hVQ a ha c
      (by rw [conjSubgroup_one]; exact hc))
  exact conjSubgroup_eq_self_iff.mpr (H.le_normalizer_omega hmem)

theorem false_of_sigmaCommIn (hGold : GoldschmidtInput) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (o2 : pCore 2 G = ⊥)
    (hS : SigmaCommIn M (omegaOneSub U)) : False :=
  H.not_weaklyClosed hGold hCen hU o2 (weaklyClosed_omega H hCen hU hS)

end SigmaCommIn

end Certificates34

theorem orderOf_mul_uniform {V : Subgroup G} (hVe : ∀ v ∈ V, v * v = 1) (hroot : IsRootTypeTI V)
    {R : Subgroup G} : ∀ m : ℕ, ∀ g h : G, conjSubgroup g V ≤ R → conjSubgroup h V ≤ R →
      conjSubgroup g V ≠ conjSubgroup h V →
      ∀ α ∈ conjSubgroup g V, α ≠ 1 → ∀ β ∈ conjSubgroup h V, β ≠ 1 →
        orderOf (α * β) = 2 ^ m →
      ∀ a ∈ conjSubgroup g V, a ≠ 1 → ∀ b ∈ conjSubgroup h V, b ≠ 1 →
        orderOf (a * b) = 2 ^ m := by
  have hTI := hroot.1
  have hsq : ∀ (g : G), ∀ a ∈ conjSubgroup g V, a * a = 1 := fun g a ha =>
    mul_self_of_mem_conj hVe ha
  have hinv : ∀ (g : G), ∀ a ∈ conjSubgroup g V, a⁻¹ = a := fun g a ha =>
    inv_eq_of_mul_eq_one_left (hsq g a ha)
  have hinf : ∀ g h : G, conjSubgroup g V ≠ conjSubgroup h V →
      conjSubgroup g V ⊓ conjSubgroup h V = ⊥ := fun g h hne => by
    by_contra h'
    exact hne (conjSubgroup_eq_of_inf_ne_bot hTI h')
  have hnorm : ∀ g h : G, ∀ x ∈ conjSubgroup g V, x ≠ 1 →
      conjSubgroup x (conjSubgroup h V) = conjSubgroup h V →
      ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a := by
    intro g h x hx hx1 heq
    refine commute_of_isRootTypeTI hroot fun hbot => ?_
    have : x ∈ conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup h V : Set G) :=
      ⟨hx, conjSubgroup_eq_self_iff.mp heq⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hx1 this
  have hcomm_of : ∀ g h : G, ∀ x ∈ conjSubgroup g V, x ≠ 1 → ∀ y ∈ conjSubgroup h V, y ≠ 1 →
      x * y = y * x → ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a := by
    intro g h x hx hx1 y hy hy1 hxy
    refine hnorm g h x hx hx1 ?_
    rw [← conjSubgroup_mul]
    refine conjSubgroup_eq_of_inf_ne_bot hTI fun hbot => hy1 ?_
    have hmem : y ∈ conjSubgroup (x * h) V ⊓ conjSubgroup h V := by
      refine Subgroup.mem_inf.mpr ⟨?_, hy⟩
      rw [conjSubgroup_mul, mem_conjSubgroup]
      have : x⁻¹ * y * x = y := by
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
          _ = x⁻¹ * (x * y) := by rw [hxy]
          _ = y := by group
      rw [this]
      exact hy
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hconjle : ∀ (z : G) (A : Subgroup G), z ∈ R → A ≤ R → conjSubgroup z A ≤ R := by
    intro z A hz hA y hy
    rw [mem_conjSubgroup] at hy
    rw [show y = z * (z⁻¹ * y * z) * z⁻¹ by group]
    exact R.mul_mem (R.mul_mem hz (hA hy)) (R.inv_mem hz)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro g h hgR hhR hne α hα hα1 β hβ hβ1 hαβ
  have hαβ1 : α * β ≠ 1 := by
    intro h1
    have : α = β := by
      calc α = α * β * β⁻¹ := by group
        _ = β := by rw [h1, one_mul, hinv h β hβ]
    have hmem : α ∈ conjSubgroup g V ⊓ conjSubgroup h V := ⟨hα, this ▸ hβ⟩
    rw [hinf g h hne, Subgroup.mem_bot] at hmem
    exact hα1 hmem
  by_cases hAB : ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a
  ·
    have hord2 : ∀ a ∈ conjSubgroup g V, a ≠ 1 → ∀ b ∈ conjSubgroup h V, b ≠ 1 →
        orderOf (a * b) = 2 := by
      intro a ha ha1 b hb hb1
      refine orderOf_eq_prime ?_ ?_
      · rw [sq, mul_assoc, ← mul_assoc b, ← hAB a ha b hb, mul_assoc, hsq h b hb, mul_one,
          hsq g a ha]
      · intro h1
        have : a = b := by
          calc a = a * b * b⁻¹ := by group
            _ = b := by rw [h1, one_mul, hinv h b hb]
        have hmem : a ∈ conjSubgroup g V ⊓ conjSubgroup h V := ⟨ha, this ▸ hb⟩
        rw [hinf g h hne, Subgroup.mem_bot] at hmem
        exact ha1 hmem
    have hm : 2 ^ m = 2 := by rw [← hαβ, hord2 α hα hα1 β hβ hβ1]
    intro a ha ha1 b hb hb1
    rw [hord2 a ha ha1 b hb hb1, hm]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hαβ
    exact hαβ1 hαβ
  have hm1 : m ≠ 1 := by
    rintro rfl
    apply hAB
    refine hcomm_of g h α hα hα1 β hβ hβ1 ?_
    have h2 : (α * β) ^ 2 = 1 := by rw [← pow_one 2, ← hαβ]; exact pow_orderOf_eq_one _
    have : α * β * (α * β) = 1 := by rw [← sq]; exact h2
    calc α * β = α * β * (α * β) * (β⁻¹ * α⁻¹) := by group
      _ = β * α := by rw [this, one_mul, hinv h β hβ, hinv g α hα]
  have hm2 : 2 ≤ m := by omega
  have hβgR : conjSubgroup (β * g) V ≤ R := by
    rw [conjSubgroup_mul]
    exact hconjle β _ (hhR hβ) hgR
  have hAβ : conjSubgroup (β * g) V ≠ conjSubgroup g V := by
    intro heq
    apply hAB
    intro a ha b hb
    refine (hnorm h g β hβ hβ1 ?_ b hb a ha).symm
    rw [← conjSubgroup_mul]
    exact heq
  have hxβ : ∀ x ∈ conjSubgroup g V, x ≠ 1 → orderOf (x * β) = 2 ^ m := by
    have hα' : β * α * β⁻¹ ∈ conjSubgroup (β * g) V := by
      rw [conjSubgroup_mul, mem_conjSubgroup]
      group
      exact hα
    have hα'1 : β * α * β⁻¹ ≠ 1 := by
      intro h1
      apply hα1
      calc α = β⁻¹ * (β * α * β⁻¹) * β := by group
        _ = 1 := by rw [h1]; group
    have hαα' : orderOf (α * (β * α * β⁻¹)) = 2 ^ (m - 1) := by
      rw [hinv h β hβ, show α * (β * α * β) = (α * β) ^ 2 by rw [sq]; group]
      exact orderOf_sq_of_orderOf_eq (by omega) hαβ
    have hIH := ih (m - 1) (by omega) g (β * g) hgR hβgR hAβ.symm α hα hα1 (β * α * β⁻¹) hα'
      hα'1 hαα'
    intro x hx hx1
    have hx' : β * x * β⁻¹ ∈ conjSubgroup (β * g) V := by
      rw [conjSubgroup_mul, mem_conjSubgroup]
      group
      exact hx
    have hx'1 : β * x * β⁻¹ ≠ 1 := by
      intro h1
      apply hx1
      calc x = β⁻¹ * (β * x * β⁻¹) * β := by group
        _ = 1 := by rw [h1]; group
    have h1 := hIH x hx hx1 _ hx' hx'1
    rw [hinv h β hβ, show x * (β * x * β) = (x * β) ^ 2 by rw [sq]; group] at h1
    have := orderOf_eq_of_orderOf_sq (by omega) h1
    rwa [Nat.sub_add_cancel (by omega)] at this
  intro x hx hx1 y hy hy1
  have hBx : conjSubgroup (x * h) V ≠ conjSubgroup h V := by
    intro heq
    apply hAB
    refine hnorm g h x hx hx1 ?_
    rw [← conjSubgroup_mul]
    exact heq
  have hβ' : x * β * x⁻¹ ∈ conjSubgroup (x * h) V := by
    rw [conjSubgroup_mul, mem_conjSubgroup]
    group
    exact hβ
  have hβ'1 : x * β * x⁻¹ ≠ 1 := by
    intro h1
    apply hβ1
    calc β = x⁻¹ * (x * β * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have hββ' : orderOf (β * (x * β * x⁻¹)) = 2 ^ (m - 1) := by
    rw [hinv g x hx, show β * (x * β * x) = (β * x) ^ 2 by rw [sq]; group]
    refine orderOf_sq_of_orderOf_eq (by omega) ?_
    rw [orderOf_mul_comm']
    exact hxβ x hx hx1
  have hxhR : conjSubgroup (x * h) V ≤ R := by
    rw [conjSubgroup_mul]
    exact hconjle x _ (hgR hx) hhR
  have hIH := ih (m - 1) (by omega) h (x * h) hhR hxhR hBx.symm β hβ hβ1 (x * β * x⁻¹) hβ'
    hβ'1 hββ'
  have hy' : x * y * x⁻¹ ∈ conjSubgroup (x * h) V := by
    rw [conjSubgroup_mul, mem_conjSubgroup]
    group
    exact hy
  have hy'1 : x * y * x⁻¹ ≠ 1 := by
    intro h1
    apply hy1
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have h1 := hIH y hy hy1 _ hy' hy'1
  rw [hinv g x hx, show y * (x * y * x) = (y * x) ^ 2 by rw [sq]; group] at h1
  have := orderOf_eq_of_orderOf_sq (by omega) h1
  rw [Nat.sub_add_cancel (by omega)] at this
  rw [orderOf_mul_comm']
  exact this

section Certificates34'

namespace R2

variable {M B : Subgroup G} (h : R2 M B)
include h

theorem exists_noncomm (hGold : GoldschmidtInput) :
    ∃ S : Sylow 2 M, ∃ A D : Subgroup G, A ∈ Lam M B ∧ D ∈ Lam M B ∧
      A ≤ (S : Subgroup M).map M.subtype ∧ D ≤ (S : Subgroup M).map M.subtype ∧
      ¬ ∀ a ∈ A, ∀ d ∈ D, a * d = d * a := by
  by_contra hcon
  have hS : SigmaCommIn M (omegaOneSub (omegaTwoSub B)) := by
    intro R hRM hR g k hg hk a ha b hb
    obtain ⟨P, hP⟩ := (hR.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
    have hle : ∀ x ∈ R, x ∈ (P : Subgroup M).map M.subtype := fun x hx =>
      ⟨⟨x, hRM hx⟩, hP hx, rfl⟩
    by_contra hne
    refine hcon ⟨P, conjSubgroup g (omegaOneSub (omegaTwoSub B)),
      conjSubgroup k (omegaOneSub (omegaTwoSub B)), ?_, ?_, fun z hz => hle z (hg hz),
      fun z hz => hle z (hk hz), fun hall => hne (hall a ha b hb)⟩
    · exact ⟨g, by rw [h.omegaOne_omegaTwo], le_trans hg hRM⟩
    · exact ⟨k, by rw [h.omegaOne_omegaTwo], le_trans hk hRM⟩
  exact SigmaCommIn.false_of_sigmaCommIn h.s3hyp hGold CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput h.H.o2 hS

end R2

end Certificates34'

end CFSG.CGT.PushingUpLit.SolKR2
