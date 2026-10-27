module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SuzModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Eq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23JSide
public import CFSG.Sporadic.SuzOddCore.CTIFirst
public import CFSG.Sporadic.SuzOddCore.CTISecond
public import CFSG.Sporadic.SuzOddCore.SmallModel

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit
  CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.CatFactsL4U4.OutInv
open scoped commutatorElement

theorem commutatorElement_mul_mul {E : Type*} [Group E] {x y k k' : E} (h1 : Commute k y)
    (h2 : Commute k k') (h3 : Commute k' x) : ⁅x * k, y * k'⁆ = ⁅x, y⁆ := by
  have c : Commute k (y * k') := h1.mul_right h2
  have d : Commute k' x⁻¹ := h3.inv_right
  calc ⁅x * k, y * k'⁆ = x * (k * (y * k')) * k⁻¹ * x⁻¹ * (y * k')⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x * (y * k') * x⁻¹ * (y * k')⁻¹ := by rw [c.eq]; group
    _ = x * y * (k' * x⁻¹) * k'⁻¹ * y⁻¹ := by group
    _ = ⁅x, y⁆ := by rw [d.eq, commutatorElement_def]; group

theorem le_of_map_le {E Q : Type*} [Group E] [Group Q] (ρ : E →* Q) {B L : Subgroup E}
    (hB : ⁅B, B⁆ = B) (hBL : B.map ρ ≤ L.map ρ) (hBk : ∀ b ∈ B, ∀ k ∈ ρ.ker, Commute k b)
    (hk : ∀ k ∈ ρ.ker, ∀ k' ∈ ρ.ker, Commute k k') : B ≤ L := by
  rw [← hB, Subgroup.commutator_le]
  intro b₁ hb₁ b₂ hb₂
  obtain ⟨l₁, hl₁, he₁⟩ := hBL ⟨b₁, hb₁, rfl⟩
  obtain ⟨l₂, hl₂, he₂⟩ := hBL ⟨b₂, hb₂, rfl⟩
  have hk₁ : b₁⁻¹ * l₁ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he₁, inv_mul_cancel]
  have hk₂ : b₂⁻¹ * l₂ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he₂, inv_mul_cancel]
  have e : ⁅b₁, b₂⁆ = ⁅l₁, l₂⁆ := by
    rw [← commutatorElement_mul_mul (hBk b₂ hb₂ _ hk₁) (hk _ hk₁ _ hk₂) (hBk b₁ hb₁ _ hk₂),
      mul_inv_cancel_left, mul_inv_cancel_left]
  rw [e, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hl₁ hl₂) (inv_mem hl₁)) (inv_mem hl₂)

theorem commutatorElement_mem_of_index_two {G : Type*} [Group G] {K D : Subgroup G}
    (hD : (D.subgroupOf K).index = 2) {x y : G} (hx : x ∈ K) (hy : y ∈ K) : ⁅x, y⁆ ∈ D := by
  have h := commutator_le_of_index_two hD
    (Subgroup.commutator_mem_commutator (mem_top (⟨x, hx⟩ : ↥K)) (mem_top (⟨y, hy⟩ : ↥K)))
  rw [mem_subgroupOf] at h
  exact h

theorem component_le_suzL
    {B : Subgroup ↥(invE 0)} (hB : IsComponent B) : B ≤ suzL.subgroupOf (invE 0) := by
  have hLE : suzL ≤ invE 0 := by
    rw [invE_eq_centM (by norm_num)]
    exact suzL_le_centM
  set L₀ := suzL.subgroupOf (invE 0) with hL₀
  have hBB : ⁅B, B⁆ = B := by
    rw [← Subgroup.map_subtype_commutator, hB.1.1.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hk4 := card_ker_rho0
  have hkp : IsPGroup 2 rho0.ker := IsPGroup.of_card (n := 2) (by rw [hk4]; norm_num)
  have hBk : ∀ b ∈ B, ∀ k ∈ rho0.ker, Commute k b := by
    rcases LocalCores.component_normal_subgroup hB (MonoidHom.normal_ker rho0) with h | h
    · exact absurd hB (not_isComponent_of_le_pgroup hkp h)
    · intro b hb k hk
      have := Subgroup.commutator_mem_commutator hb hk
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
  have hkk : ∀ k ∈ rho0.ker, ∀ k' ∈ rho0.ker, Commute k k' := by
    have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := rho0.ker)
      (by rw [hk4]; norm_num)
    intro k hk k' hk'
    exact congrArg Subtype.val (hc.is_comm.comm ⟨k, hk⟩ ⟨k', hk'⟩)
  have hcL : Nat.card L₀ = 20160 := by
    rw [hL₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLE).toEquiv, card_suzL]
  have hsL : IsSimpleGroup ↥L₀ := by
    have := isSimpleGroup_suzL
    exact (Subgroup.subgroupOfEquivOfLe hLE).isSimpleGroup
  set ρL := rho0.comp L₀.subtype with hρL
  have hinj : Function.Injective ρL := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρL.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).1 h
    · exfalso
      have hle : L₀ ≤ rho0.ker := fun l hl => by
        have : (⟨l, hl⟩ : ↥L₀) ∈ ρL.ker := h ▸ mem_top _
        exact this
      have := Subgroup.card_le_of_le hle
      rw [hcL, hk4] at this
      omega
  set D' := L₀.map rho0 with hD'
  have hcD : Nat.card D' = 20160 := by
    have e1 : ρL.range = D' := by rw [hρL, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcL]
  have hDK : D' ≤ rho0.range := Subgroup.map_le_range rho0 L₀
  have hidx : (D'.subgroupOf rho0.range).index = 2 := by
    have h := (D'.subgroupOf rho0.range).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hcD, card_range_rho0] at h
    omega
  refine le_of_map_le rho0 hBB ?_ hBk hkk
  rw [← hBB, Subgroup.map_commutator, Subgroup.commutator_le]
  intro x hx y hy
  exact commutatorElement_mem_of_index_two hidx (Subgroup.map_le_range rho0 B hx)
    (Subgroup.map_le_range rho0 B hy)

theorem isComponent_centralizer_subgroupOf {G : Type*} [Group G] {X J : Subgroup G} {α : G}
    (hαX : α ∈ X) (hJX : J ≤ X) (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))) :
    IsComponent ((J.subgroupOf X).subgroupOf (centralizer ({(⟨α, hαX⟩ : ↥X)} : Set ↥X))) := by
  set C := centralizer ({α} : Set G) with hC
  set CX := centralizer ({(⟨α, hαX⟩ : ↥X)} : Set ↥X) with hCX
  let κ : ↥CX →* ↥C :=
    { toFun := fun x => ⟨((x : ↥X) : G), mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hκ : Function.Injective κ := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥C => (z : G)) hxy))
  set B := (J.subgroupOf X).subgroupOf CX with hB
  have hcomap : B = (J.subgroupOf C).comap κ := by
    ext x
    exact Iff.rfl
  have hmap : B.map κ = J.subgroupOf C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcomap] at hx
      exact hx
    · intro hy
      have hyJ : (y : G) ∈ J := hy
      refine ⟨⟨⟨y, hJX hyJ⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 y.2))⟩, hyJ, rfl⟩
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv
    ((B.equivMapOfInjective κ hκ).trans (MulEquiv.subgroupCongr hmap)).symm hJ.1, ?_⟩
  rw [hcomap]
  exact hJ.2.comap κ

theorem suz_fusion
    {X : Type*} [Group X] (e : X ≃* Blueprint.NativeSporadic.Suz) {α ζ : X}
    (hα : orderOf α = 2) {B : Subgroup ↥(centralizer ({α} : Set X))} (hB : IsComponent B)
    (hζC : ζ ∈ centralizer ({α} : Set X))
    (hζB : (⟨ζ, hζC⟩ : ↥(centralizer ({α} : Set X))) ∈ B) (hζ2 : ζ * ζ = 1) :
    ∃ γ : X, γ⁻¹ * α * γ = α * ζ := by
  by_cases hζ1 : ζ = 1
  · exact ⟨1, by rw [hζ1]; group⟩
  set f : X ≃* suzM := e.trans suzEquivM with hf
  set a' : Equiv.Perm (Fin 1782) := (f α : Equiv.Perm (Fin 1782)) with ha'
  have ha'2 : orderOf a' = 2 := by rw [ha', Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hα]
  obtain ⟨c, hcT, h01⟩ := suzM_involution_class (f α).2 ha'2
  set ψ : X →* Equiv.Perm (Fin 1782) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (suzM.subtype.comp f.toMonoidHom) with hψdef
  have hψ : ∀ x, ψ x = c⁻¹ * (f x : Equiv.Perm (Fin 1782)) * c := fun x => by
    simp [hψdef]
  have hψi : Function.Injective ψ := by
    intro x y hxy
    rw [hψ, hψ, mul_left_inj, mul_right_inj] at hxy
    exact f.injective (Subtype.ext hxy)
  have key : ∀ i < 4, c * suzInv i * c⁻¹ = a' →
      (centralizer ({α} : Set X)).map ψ = invE i := by
    intro i hi hci
    rw [invE_eq_centM hi]
    have hti : suzInv i = c⁻¹ * a' * c := by rw [← hci]; group
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxα : x * α = α * x := mem_centralizer_singleton_iff.1 hx
      have hfx : (f x : Equiv.Perm (Fin 1782)) * a' = a' * f x := by
        rw [ha', ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hxα]
      refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
      · rw [hψ, hti]
        calc c⁻¹ * (f x : Equiv.Perm (Fin 1782)) * c * (c⁻¹ * a' * c) =
            c⁻¹ * ((f x : Equiv.Perm (Fin 1782)) * a') * c := by group
          _ = c⁻¹ * (a' * f x) * c := by rw [hfx]
          _ = c⁻¹ * a' * c * (c⁻¹ * (f x : Equiv.Perm (Fin 1782)) * c) := by group
      · rw [hψ]
        have := (suzM_conj_iff (inv_mem hcT) (f x : Equiv.Perm (Fin 1782))).1 (f x).2
        rwa [inv_inv] at this
    · rintro ⟨hyc, hyM⟩
      have hyt : y * suzInv i = suzInv i * y := mem_centralizer_singleton_iff.1 hyc
      have hz : c * y * c⁻¹ ∈ suzM := (suzM_conj_iff hcT y).1 hyM
      refine ⟨f.symm ⟨c * y * c⁻¹, hz⟩, mem_centralizer_singleton_iff.2 ?_, ?_⟩
      · apply f.injective
        apply Subtype.ext
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul]
        change c * y * c⁻¹ * a' = a' * (c * y * c⁻¹)
        rw [← hci]
        calc c * y * c⁻¹ * (c * suzInv i * c⁻¹) = c * (y * suzInv i) * c⁻¹ := by group
          _ = c * (suzInv i * y) * c⁻¹ := by rw [hyt]
          _ = c * suzInv i * c⁻¹ * (c * y * c⁻¹) := by group
      · rw [hψ, MulEquiv.apply_symm_apply]
        change c⁻¹ * (c * y * c⁻¹) * c = y
        group
  have iso : ∀ i < 4, c * suzInv i * c⁻¹ = a' →
      ∃ Φ : ↥(centralizer ({α} : Set X)) ≃* ↥(invE i),
        ∀ x, (Φ x : Equiv.Perm (Fin 1782)) = ψ x := fun i hi hci =>
    ⟨((centralizer ({α} : Set X)).equivMapOfInjective ψ hψi).trans
      (MulEquiv.subgroupCongr (key i hi hci)), fun _ => rfl⟩
  rcases h01 with h0 | h1
  · obtain ⟨Φ, hΦ⟩ := iso 0 (by norm_num) h0
    have hle := component_le_suzL (LocalCores.isComponent_map_mulEquiv Φ hB)
    have hζ₀ : ψ ζ ∈ suzL := by
      have := hle ⟨⟨ζ, hζC⟩, hζB, rfl⟩
      rw [mem_subgroupOf] at this
      change ((Φ ⟨ζ, hζC⟩ : ↥(invE 0)) : Equiv.Perm (Fin 1782)) ∈ suzL at this
      rwa [hΦ] at this
    have hζ₀2 : ψ ζ * ψ ζ = 1 := by rw [← map_mul, hζ2, map_one]
    have hζ₀1 : ψ ζ ≠ 1 := fun h => hζ1 (hψi (h.trans (map_one ψ).symm))
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_conj_suzL sY1_mem hζ₀ sY1_mul_self hζ₀2 sY1_ne_one hζ₀1
    have hℓt : ℓ * suzInv 0 = suzInv 0 * ℓ :=
      mem_centralizer_singleton_iff.1 (suzL_le_centM hℓL).1
    have hγ₀M : ℓ * sMm ∈ suzM := mul_mem (suzL_le_centM hℓL).2 sMm_mem
    have hγ₀t : ℓ * sMm * suzInv 0 * (ℓ * sMm)⁻¹ = suzInv 0 * ψ ζ := by
      rw [← hℓ]
      calc ℓ * sMm * suzInv 0 * (ℓ * sMm)⁻¹ = ℓ * (sMm * suzInv 0 * sMm⁻¹) * ℓ⁻¹ := by group
        _ = ℓ * (suzInv 0 * sY1) * ℓ⁻¹ := by rw [sMm_conj]
        _ = ℓ * suzInv 0 * sY1 * ℓ⁻¹ := by group
        _ = suzInv 0 * (ℓ * sY1 * ℓ⁻¹) := by rw [hℓt]; group
    have hγ₁M : c * (ℓ * sMm) * c⁻¹ ∈ suzM := (suzM_conj_iff hcT _).1 hγ₀M
    refine ⟨(f.symm ⟨c * (ℓ * sMm) * c⁻¹, hγ₁M⟩)⁻¹, ?_⟩
    rw [inv_inv]
    apply f.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
    change c * (ℓ * sMm) * c⁻¹ * a' * (c * (ℓ * sMm) * c⁻¹)⁻¹ =
      a' * (f ζ : Equiv.Perm (Fin 1782))
    have hfζ : (f ζ : Equiv.Perm (Fin 1782)) = c * ψ ζ * c⁻¹ := by rw [hψ]; group
    rw [hfζ, ha', ← h0]
    calc c * (ℓ * sMm) * c⁻¹ * (c * suzInv 0 * c⁻¹) * (c * (ℓ * sMm) * c⁻¹)⁻¹ =
        c * (ℓ * sMm * suzInv 0 * (ℓ * sMm)⁻¹) * c⁻¹ := by group
      _ = c * (suzInv 0 * ψ ζ) * c⁻¹ := by rw [hγ₀t]
      _ = c * suzInv 0 * c⁻¹ * (c * ψ ζ * c⁻¹) := by group
  · obtain ⟨Φ, -⟩ := iso 1 (by norm_num) h1
    exact absurd (LocalCores.isComponent_map_mulEquiv Φ hB)
      (CTI_Suz_second_involution_centralizer_has_no_components.2 _)

theorem fus23ConclW_of_Suz
    {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)
    (hT : ¬ h.Table54) (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2)
    (hαN : phi hKa (abar h) ∈ NL hKa)
    (hSuz : Nonempty (↥(NL hKa) ≃* Blueprint.NativeSporadic.Suz)) : h.Fus23ConclW := by
  obtain ⟨e⟩ := hSuz
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hZK : center (OddBar h.K) = ⊥ := by
    by_contra hne
    exact hT (Or.inr (Or.inr (Or.inl ⟨hL, hKa, hne, ⟨eZ.symm.trans (eN.symm.trans e)⟩⟩)))
  obtain ⟨-, -, -, d, -, -, -, hdD, -, hd2, hdx, hdP⟩ := exists_fixed_D h hL
  obtain ⟨hζJ, hζ2, hcomm, -⟩ := zeta_facts hKa hZK hdD hd2 hdP
  set ζ := phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩) with hζ
  have hB := isComponent_centralizer_subgroupOf hαN (Jhat_le_NL hKa) (Jhat_component hKa).2
  have hζN : ζ ∈ NL hKa := Jhat_le_NL hKa hζJ
  have hα : orderOf (⟨phi hKa (abar h), hαN⟩ : ↥(NL hKa)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_phi_abar' hKa
  have hζC : (⟨ζ, hζN⟩ : ↥(NL hKa)) ∈
      centralizer ({(⟨phi hKa (abar h), hαN⟩ : ↥(NL hKa))} : Set ↥(NL hKa)) :=
    mem_centralizer_singleton_iff.2 (Subtype.ext hcomm.symm)
  obtain ⟨γ, hγ⟩ := suz_fusion e hα hB hζC hζJ (Subtype.ext hζ2)
  refine fus23ConclW_of_NL hKa hZK hdD hd2 hdx hdP (γ := (γ : ↥(GAut hKa))) γ.2 ?_
  have := congrArg (fun y : ↥(NL hKa) => (y : ↥(GAut hKa))) hγ
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

end CFSG.ComponentClassification.GSThmB.CF23L34
