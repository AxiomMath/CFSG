module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Inj
public import CFSG.ClassicalInvolution.Q3.TL3T35

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


namespace Lab

section Gen

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem toHom_of_pSpan_eq_top {n : ℕ} (hgen : TC.Thin.pSpan Φ = ⊤)
    (φ : ↥(TC.Thin.pSpan Φ) →* AE.AEQ n) (hker : φ.ker ≤ Subgroup.center ↥(TC.Thin.pSpan Φ)) :
    ∃ f : X →* AE.AEQ n, f.ker ≤ Subgroup.center X ∧
      ∀ L : Subgroup X, (L.subgroupOf (TC.Thin.pSpan Φ)).map φ = L.map f := by
  have hmem : ∀ x : X, x ∈ TC.Thin.pSpan Φ := fun x => hgen ▸ Subgroup.mem_top x
  let ε : X →* ↥(TC.Thin.pSpan Φ) :=
    { toFun := fun x => ⟨x, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hεinj : Function.Injective ε := fun x y h => congrArg Subtype.val h
  refine ⟨φ.comp ε, ?_, fun L => ?_⟩
  · intro x hx
    have hx' : ε x ∈ φ.ker := hx
    have hc := hker hx'
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    exact hεinj (by rw [map_mul, map_mul]; exact hc (ε g))
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.1, Subgroup.mem_subgroupOf.mp hz, by
        show φ (ε z.1) = φ z
        rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ε x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem mem_normalizer_of_comm {G : Type} [Group G] {L : Subgroup G} {x : G}
    (hc : ∀ y ∈ L, x * y = y * x) : x ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hc y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := hc _ hy
    have h2 : x * y * x⁻¹ = y :=
      mul_left_cancel (h1.trans (show x * y * x⁻¹ * x = x * y by group))
    rwa [h2] at hy

theorem injOn {n : ℕ} (hn : 5 ≤ n) (f : X →* AE.AEQ n) {L : Subgroup X} (h8 : Nat.card ↥L = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} (hlab : L.map f = AE.memBar α h b) {l₁ l₂ : X}
    (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L) (he : f l₁ = f l₂) : l₁ = l₂ := by
  let g : ↥L → ↥(AE.memBar α h b) := fun x => ⟨f x, by rw [← hlab]; exact ⟨x, x.2, rfl⟩⟩
  have hg : Function.Surjective g := by
    rintro ⟨x, hx⟩
    rw [← hlab] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcard : Nat.card ↥L ≤ Nat.card ↥(AE.memBar α h b) := by
    rw [AE.natCard_memBar hn, h8]
  have hinj := (hg.bijective_of_nat_card_le hcard).1
  have := @hinj ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ (Subtype.ext he)
  exact congrArg Subtype.val this

theorem map_eq_zBar {n : ℕ} (hn : 5 ≤ n) (f : X →* AE.AEQ n) {L : Subgroup X} (h8 : Nat.card ↥L = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} (hlab : L.map f = AE.memBar α h b) {u : X}
    (hu : IsUniqueInvolution L u) : f u = AE.zBar α h := by
  have hmem : f u ∈ AE.memBar α h b := by
    rw [← hlab]
    exact Subgroup.mem_map_of_mem f hu.mem
  have hsq : f u * f u = 1 := by rw [← map_mul, hu.sq, map_one]
  rcases AE.eq_of_mem_memBar_mul_self hn hmem hsq with h1 | h1
  · exfalso
    exact hu.ne_one (injOn hn f h8 hlab hu.mem L.one_mem (h1.trans (map_one f).symm))
  · exact h1

theorem commutes_of_map_comm (hC : TwinSecCtx X Φ) {n : ℕ} (f : X →* AE.AEQ n)
    (hN2 : IsPGroup 2 ↥f.ker) {M M' : Subgroup X} (hM : M ∈ Φ) (hM' : M' ∈ Φ) (hne : M ≠ M')
    (hc : ∀ x ∈ M.map f, ∀ y ∈ M'.map f, x * y = y * x) : Commutes M M' := by
  have hm : ∀ {L : Subgroup X}, L ∈ Φ → IsPGroup 2 ↥(L.map f) := fun hL => (hC.two _ hL).map f
  have hN : M.map f ≤ Subgroup.normalizer (M'.map f : Set (AE.AEQ n)) :=
    fun x hx => mem_normalizer_of_comm (hc x hx)
  have hsup : IsPGroup 2 ↥(M.map f ⊔ M'.map f) := (hm hM).to_sup_of_normal_right' (hm hM') hN
  have hP : IsPGroup 2 ↥((M.map f ⊔ M'.map f).comap f) := hsup.comap_of_ker_isPGroup f hN2
  exact TL4.commutes_of_le_two hC.S.hyp hC.two hM hM' hne hP
    (fun x hx => Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem f hx)))
    (fun x hx => Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem f hx)))

end Gen

end Lab

theorem false_of_labelled {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hC : TwinSecCtx X Φ) {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) {𝒜 : Set (Finset (Fin n))}
    (f : X →* AE.AEQ n) (hker : f.ker ≤ Subgroup.center X)
    (hlabel : ∀ L ∈ Φ, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool), L.map f = AE.memBar α h b)
    (hsurj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Φ, L.map f = AE.memBar α h b)
    (hM : AENC4 n 𝒜) : False := by
  have hN2 : IsPGroup 2 ↥f.ker := (TL4.Vtx.isPGroup_center_of_oddFree hC.S.oddFree).to_le hker
  have h8 : ∀ L ∈ Φ, Nat.card ↥L = 8 := by
    intro L hL
    obtain ⟨e⟩ := hC.q8 L hL
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hz : ∀ K ∈ Φ, ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      K.map f = AE.memBar α h b → ∀ z : X, IsUniqueInvolution K z → f z = AE.zBar α h :=
    fun K hK α h b hl z hzK => Lab.map_eq_zBar hn f (h8 K hK) hl hzK
  have hno : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → z ∉ f.ker := by
    intro K hK z hzK hzk
    obtain ⟨α, -, h, b, hl⟩ := hlabel K hK
    have h1 := hz K hK α h b hl z hzK
    rw [MonoidHom.mem_ker] at hzk
    exact AE.zBar_ne_one hn α h (h1.symm.trans hzk)
  have hinj : ∀ M ∈ Φ, ∀ M' ∈ Φ, M.map f = M'.map f → M = M' :=
    (inj_members_of_twoGroupKernel hC.S hC.two f hN2 hno).2
  obtain ⟨α, β, hα, hβ, hα𝒜, hβ𝒜, hαβ, b₁, y, hy, hyy, hyβ⟩ := hM
  obtain ⟨L₁, hL₁, hL₁f⟩ := hsurj α hα𝒜 hα b₁
  obtain ⟨L₂, hL₂, hL₂f⟩ := hsurj β hβ𝒜 hβ true
  obtain ⟨L₂', hL₂', hL₂'f⟩ := hsurj β hβ𝒜 hβ false
  obtain ⟨y₁, hy₁L, hy₁f⟩ : y ∈ L₁.map f := by
    rw [hL₁f]
    exact hy
  obtain ⟨s₂, hs₂⟩ := hC.exists_inv hL₂
  have hfs₂ : f s₂ = AE.zBar β hβ := hz L₂ hL₂ β hβ true hL₂f s₂ hs₂
  have hfsq : f (y₁ * y₁) = AE.zBar α hα := by rw [map_mul, hy₁f, hyy]
  have hcomm_f : f y₁ * f s₂ = f s₂ * f y₁ := by
    rw [hy₁f, hfs₂]
    exact hyβ
  have hsq_ne : y₁ * y₁ ≠ 1 := by
    intro h
    have h1 : f (y₁ * y₁) = 1 := by rw [h, map_one]
    exact AE.zBar_ne_one hn α hα (hfsq.symm.trans h1)
  have hpow4 : y₁ ^ 4 = 1 := by
    have h4 : f (y₁ ^ 4) = f 1 := by
      rw [show y₁ ^ 4 = (y₁ * y₁) * (y₁ * y₁) by simp [pow_succ, mul_assoc], map_mul, hfsq,
        AE.zBar_mul_self, map_one]
    exact Lab.injOn hn f (h8 L₁ hL₁) hL₁f (L₁.pow_mem hy₁L 4) L₁.one_mem h4
  have hord : orderOf y₁ = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := y₁)
      (by
        intro h1
        apply hsq_ne
        simpa [pow_two] using h1)
      (by simpa using hpow4)
    simpa using h
  have hne_sq : s₂ ≠ y₁ * y₁ := by
    intro h
    apply hαβ
    refine AE.eq_of_zBar_eq hn8 (h := hα) (h' := hβ) ?_
    rw [← hfsq, ← h, hfs₂]
  have hconj : y₁ * s₂ * y₁⁻¹ = s₂ := by
    have hAΦ : conjSub y₁ L₂ ∈ Φ := hC.S.hyp.conjInvariant y₁ L₂ hL₂
    have hcs : IsUniqueInvolution (conjSub y₁ L₂) (y₁ * s₂ * y₁⁻¹) := hs₂.conj y₁
    obtain ⟨γ, -, hγ, b₃, hAf⟩ := hlabel _ hAΦ
    have hfc : f (y₁ * s₂ * y₁⁻¹) = AE.zBar γ hγ := hz _ hAΦ γ hγ b₃ hAf _ hcs
    have hfc' : f (y₁ * s₂ * y₁⁻¹) = AE.zBar β hβ := by
      rw [map_mul, map_mul, map_inv, hcomm_f, mul_inv_cancel_right, hfs₂]
    have hγβ : γ = β := AE.eq_of_zBar_eq hn8 (hfc.symm.trans hfc')
    subst hγβ
    cases b₃
    ·
      have hAeq : conjSub y₁ L₂ = L₂' := hinj _ hAΦ L₂' hL₂' (hAf.trans hL₂'f.symm)
      rw [hAeq] at hcs
      have hne : L₂' ≠ L₂ := by
        intro h
        apply AE.memBar_true_ne_false hn γ hγ
        rw [← hL₂f, ← hL₂'f, h]
      have hcomm : Commutes L₂' L₂ :=
        Lab.commutes_of_map_comm hC f hN2 hL₂' hL₂ hne (by
          rw [hL₂'f, hL₂f]
          exact TC.Thin.memBar_twin_comm γ hγ false)
      have hnbr : L₂' ∈ omegaNbr Φ L₂ := by
        refine ⟨hL₂', hne, L₂', TL4.mem_RSet_self hL₂' (hC.two L₂' hL₂'), le_rfl, ?_⟩
        intro x hx
        exact Lab.mem_normalizer_of_comm (fun y hy => hcomm x hx y hy)
      exact (hC.twin_inv hL₂ hnbr hs₂ hcs).symm
    ·
      have hAeq : conjSub y₁ L₂ = L₂ := hinj _ hAΦ L₂ hL₂ (hAf.trans hL₂f.symm)
      rw [hAeq] at hcs
      exact hcs.eq hs₂
  have hcomm_s : s₂ * y₁ = y₁ * s₂ := by
    calc s₂ * y₁ = (y₁ * s₂ * y₁⁻¹) * y₁ := by rw [hconj]
      _ = y₁ * s₂ := by group
  exact hC.nc4 ⟨L₁, hL₁, y₁, hy₁L, hord, L₂, hL₂, s₂, hs₂, hne_sq, hcomm_s⟩

theorem false_of_aeIdent {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hC : TwinSecCtx X Φ) {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8) (hM : AENC4 m Set.univ)
    (I : TC.Thin.AEIdent Φ m) : False := by
  have hgen : TC.Thin.pSpan Φ = ⊤ := by
    have := hC.S.gen
    unfold omegaGen at this
    exact this
  obtain ⟨f, hker, hmap⟩ := Lab.toHom_of_pSpan_eq_top hgen I.φ I.ker_le
  refine false_of_labelled hC hm hm8 f hker (fun L hL => ?_) (fun α _ h b => ?_) hM
  · obtain ⟨α, h, b, hl⟩ := I.label L hL
    exact ⟨α, Set.mem_univ α, h, b, (hmap L).symm.trans hl⟩
  · obtain ⟨L, hL, hl⟩ := I.label_surj α h b
    exact ⟨L, hL, (hmap L).symm.trans hl⟩

theorem false_of_e64 {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hC : TwinSecCtx X Φ) (hM : AENC4 7 AE.e64Sets)
    (I : TC.Thin.AEIdentOn Φ 7 AE.e64Sets AE.e64Sub) : False := by
  have hgen : TC.Thin.pSpan Φ = ⊤ := by
    have := hC.S.gen
    unfold omegaGen at this
    exact this
  obtain ⟨f, hker, hmap⟩ := Lab.toHom_of_pSpan_eq_top hgen I.φ I.ker_le
  refine false_of_labelled hC (by norm_num) (by norm_num) f hker (fun L hL => ?_)
    (fun α hα h b => ?_) hM
  · obtain ⟨α, hα, h, b, hl⟩ := I.label L hL
    exact ⟨α, hα, h, b, (hmap L).symm.trans hl⟩
  · obtain ⟨L, hL, hl⟩ := I.label_surj α hα h b
    exact ⟨L, hL, (hmap L).symm.trans hl⟩

end CFSG.ClassicalInvolution.Q8P.Asc77.P25T
