module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Diagonal
public import CFSG.LargeExtraspecial.S10EightP
public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBAltGp
public import CFSG.GroupTheory.CentralExtensionPGroup
public import CFSG.GF2Type.Smith1979.W4AsE11Surv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Swap

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5
  CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}
variable (D : S5.SwapData S g)

@[expose] def SwapW4.orb (A : Subgroup S.O) (v : S.Qt) : Set S.Qt :=
  {y | ∃ e ∈ A, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v = y}

@[expose] def SwapW4.stab (v : S.Qt) : Subgroup S.O where
  carrier := {e | (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  mul_mem' := fun {e f} he hf => by
    change (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v at he
    change (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v at hf
    change ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) * (f : S.Qt ≃ₗ[ZMod 2] S.Qt)) v = v
    rw [LinearEquiv.mul_apply, hf, he]
  one_mem' := rfl
  inv_mem' := fun {e} he => by
    change (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v at he
    change ((e : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹) v = v
    calc ((e : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹) v
        = ((e : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹) ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by rw [he]
      _ = v := by simp

theorem SwapW4.mem_stab {v : S.Qt} {e : S.O} :
    e ∈ SwapW4.stab v ↔ (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  change ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ↔
    ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
  exact Iff.rfl

theorem SwapW4.Z_inf_Xhat (W : SwapW4 D) : D.Z ⊓ D.Xhat = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzE2 : z ∈ D.Z ⊔ D.W := (D.Xhat_le_sup_inf W.H).trans inf_le_left hz.2
  obtain ⟨p, hp, huniq⟩ := SwapW4.decomp D W hzE2
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  have hdZ : z = (⟨z, hz.1⟩ : D.Z) * (D.t * (1 : D.Z) * D.t⁻¹) := by simp
  obtain ⟨u, hu⟩ := hz.2
  have hdX : z = (u : D.Z) * (D.t * (u : D.Z) * D.t⁻¹) := by
    rw [← hu, S5.SwapData.chi_apply]
  have hpZ := huniq (⟨z, hz.1⟩, 1) hdZ
  have hpX := huniq (u, u) hdX
  have hsecond := congrArg (fun q : D.Z × D.Z => ((q.2 : D.Z) : S.O)) (hpZ.trans hpX.symm)
  have hu1 : (u : S.O) = 1 := hsecond.symm
  rw [hdX, hu1]
  simp

theorem SwapW4.stabilizer_a_le_normalizer (W : SwapW4 D) :
    (D.Z ⊔ D.W) ⊓ SwapW4.stab (aV D.mem_Lbar) ≤
      normalizer (S.Lbar g : Set S.O) := by
  intro x hx
  have hxM : (x : S.O) ∈ S.Mbar :=
    (sup_le D.Z_le_Mbar D.isComponentOf_W.1) hx.1
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (show (x : S.O) ∈ S.ρ.range from hxM)
  have hfix : (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    rw [hm]
    exact hx.2
  have hN := S10.mem_normalizer_of_fix W.H hfix
  rwa [hm] at hN

theorem SwapW4.card_stab_a_le (W : SwapW4 D) :
    Nat.card ((D.Z ⊔ D.W) ⊓ SwapW4.stab (aV D.mem_Lbar) : Subgroup S.O) ≤ 48 := by
  let E : Subgroup S.O := D.Z ⊔ D.W
  let P : Subgroup D.Z := SwapW4.P D W
  let N : Subgroup D.Z := normalizer (P : Set D.Z)
  have hC_le_N : E ⊓ SwapW4.stab (aV D.mem_Lbar) ≤ normalizer (S.Lbar g : Set S.O) :=
    SwapW4.stabilizer_a_le_normalizer D W
  let f : ↥P × ↥N → S.O := fun q => (q.1.1 : S.O) * D.chi q.2.1
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨p, hpP⟩, ⟨n, hnN⟩⟩ ⟨⟨p', hp'P⟩, ⟨n', hn'N⟩⟩ h
    change (p : S.O) * D.chi n = (p' : S.O) * D.chi n' at h
    have hleft : (p : S.O)⁻¹ * p' = D.chi n * (D.chi n')⁻¹ := by
      calc (p : S.O)⁻¹ * p'
          = (p : S.O)⁻¹ * ((p' : S.O) * D.chi n') * (D.chi n')⁻¹ := by group
        _ = (p : S.O)⁻¹ * ((p : S.O) * D.chi n) * (D.chi n')⁻¹ := by rw [h]
        _ = D.chi n * (D.chi n')⁻¹ := by group
    have hX : D.chi n * (D.chi n')⁻¹ ∈ D.Xhat :=
      D.Xhat.mul_mem (D.chi_mem_Xhat n) (D.Xhat.inv_mem (D.chi_mem_Xhat n'))
    have hmem : (p : S.O)⁻¹ * p' ∈ D.Z ⊓ D.Xhat :=
      ⟨D.Z.mul_mem (D.Z.inv_mem p.2) p'.2, by rwa [hleft]⟩
    rw [SwapW4.Z_inf_Xhat D W] at hmem
    have hp_eq : p = p' := by
      apply Subtype.ext
      have h1 : (p : S.O)⁻¹ * p' = 1 := Subgroup.mem_bot.mp hmem
      have h2 : (p : S.O) * ((p : S.O)⁻¹ * p') = p' := by group
      rw [h1, mul_one] at h2
      exact h2
    have hn_eq : n = n' := by
      apply SwapW4.chi_injective D W
      have h' := h
      rw [hp_eq] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hp_eq) (Subtype.ext hn_eq)
  have hC_le_range : ((E ⊓ SwapW4.stab (aV D.mem_Lbar) : Subgroup S.O) : Set S.O) ⊆
      Set.range f := by
    intro x hx
    obtain ⟨p, hpP, n, hnN, heq⟩ :=
      SwapW4.normalizer_E2_subset D W hx.1 (hC_le_N hx)
    exact ⟨(⟨p, hpP⟩, ⟨n, hnN⟩), heq.symm⟩
  have hC_le : Nat.card ↥((D.Z ⊔ D.W) ⊓ SwapW4.stab (aV D.mem_Lbar)) ≤
      Nat.card (↥P × ↥N) := by
    have hsub := Set.ncard_le_ncard hC_le_range
    have h1 : Nat.card ↥((D.Z ⊔ D.W) ⊓ SwapW4.stab (aV D.mem_Lbar)) =
        (((D.Z ⊔ D.W) ⊓ SwapW4.stab (aV D.mem_Lbar) : Subgroup S.O) : Set S.O).ncard :=
      Nat.card_coe_set_eq _
    have h2 : Nat.card (↥P × ↥N) = (Set.range f).ncard := by
      rw [← Nat.card_coe_set_eq (Set.range f)]
      exact Nat.card_congr (Equiv.ofInjective f hf_inj)
    rw [h1, h2]
    exact hsub
  haveI : IsSimpleGroup ↥D.Z := SwapW4.isSimpleGroup_Z D W
  have hN_ne_top : N ≠ ⊤ := by
    intro hN
    have hnormal : P.Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hbot | htop
    · have hcard : Nat.card P = 1 := by rw [hbot, Subgroup.card_bot]
      rw [SwapW4.card_P D W] at hcard
      norm_num at hcard
    · have hcard : Nat.card P = Nat.card D.Z := by rw [htop, Subgroup.card_top]
      rw [SwapW4.card_P D W, SwapW4.card_Z D W] at hcard
      norm_num at hcard
  have hNcard : Nat.card ↥N ≤ 12 :=
    CFSG.LocalAnalysis.WeakClosure81.b114_ElevenFourBAltGp_card_le_twelve_of_ne_top
      (A := ↥D.Z) (SwapW4.card_Z D W) hN_ne_top
  have hprod : Nat.card (↥P × ↥N) = Nat.card ↥P * Nat.card ↥N := Nat.card_prod _ _
  rw [hprod, SwapW4.card_P D W] at hC_le
  have : 4 * Nat.card ↥N ≤ 4 * 12 := Nat.mul_le_mul_left 4 hNcard
  omega

theorem SwapW4.card_orbit_a (W : SwapW4 D) :
    75 ≤ Nat.card (SwapW4.orb (D.Z ⊔ D.W) (aV D.mem_Lbar)) := by
  classical
  let E : Subgroup S.O := D.Z ⊔ D.W
  let a : S.Qt := aV D.mem_Lbar
  letI : MulAction ↥E S.Qt :=
    MulAction.compHom (M := S.O) (N := ↥E) S.Qt (Subgroup.subtype E)
  have horb : SwapW4.orb E a = MulAction.orbit ↥E a := by
    ext y
    change (∃ e ∈ E, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) a = y) ↔
      (∃ g : ↥E, g • a = y)
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, g.2, rfl⟩
  have hstab_sub : MulAction.stabilizer ↥E a =
      (E ⊓ SwapW4.stab a).subgroupOf E := by
    ext x
    rw [MulAction.mem_stabilizer_iff]
    change ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a ↔
      (x : S.O) ∈ E ⊓ SwapW4.stab a
    constructor
    · intro h
      exact ⟨x.2, h⟩
    · rintro ⟨-, h⟩
      exact h
  have hstab_card : Nat.card (MulAction.stabilizer ↥E a) ≤ 48 := by
    rw [hstab_sub]
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ SwapW4.stab a ≤ E)).toEquiv]
    exact SwapW4.card_stab_a_le D W
  have horb_index : Nat.card (SwapW4.orb E a) =
      (MulAction.stabilizer ↥E a).index := by
    calc Nat.card (SwapW4.orb E a) = Nat.card ↥(MulAction.orbit ↥E a) := by rw [horb]
      _ = Nat.card (↥E ⧸ MulAction.stabilizer ↥E a) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥E a)
      _ = (MulAction.stabilizer ↥E a).index := (Subgroup.index_eq_card _).symm
  have hOS : (MulAction.stabilizer ↥E a).index *
      Nat.card (MulAction.stabilizer ↥E a) = Nat.card ↥E :=
    Subgroup.index_mul_card _
  have hcardE : Nat.card ↥E = 3600 := SwapW4.card_E2 D W
  rw [← horb_index, hcardE] at hOS
  change 75 ≤ Nat.card (SwapW4.orb E a)
  by_contra hlt
  push Not at hlt
  have hlt74 : Nat.card (SwapW4.orb E a) ≤ 74 := by omega
  have hle : Nat.card (SwapW4.orb E a) * Nat.card (MulAction.stabilizer ↥E a) ≤
      74 * 48 := Nat.mul_le_mul hlt74 hstab_card
  omega


theorem SwapW4.exists_x (W : SwapW4 D)
    (Q : QuadraticForm (ZMod 2) (Vt S g D.t)) (hQ : Q.polarBilin.Nondegenerate)
    (hR : RmodN S g D.t = omegaGroup Q hQ)
    (hsing : ∀ v : Vt S g D.t, v ≠ 0 →
      (Q v = 0 ↔ v ∈ orbitOf (RmodN S g D.t) (aV D.mem_Lbar)))
    (hmin : ∀ U : Submodule (ZMod 2) (Vt S g D.t), finrank (ZMod 2) U = 2 →
      ∃ u ∈ U, Q u ≠ 0) :
    ∃ x : G, x ∈ S.QG ⊓ S.Qa g ∧ orderOf x = 2 ∧ x ≠ S.z ∧
      S.cl x ≠ S.cl (g * S.z * g⁻¹) ∧
      ∃ hxV : S.cl x ∈ Vt S g D.t, Q ⟨S.cl x, hxV⟩ = 1 ∧
        ¬ ∃ ξ ∈ D.Xhat, (ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aV D.mem_Lbar) = S.cl x := by
  classical
  let Vd : Submodule (ZMod 2) S.Qt :=
    S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g D.t
  have hVd3 : finrank (ZMod 2) Vd = 3 := by
    have h := S6.finrank_clSub_inf_Vt W.H W.C D.mem_Lbar D.t_ne_one W.hVQ
    rw [W.h4] at h
    dsimp [Vd] at h ⊢
    omega
  let b := Module.finBasisOfFinrankEq (ZMod 2) Vd hVd3
  let U : Submodule (ZMod 2) Vd :=
    Submodule.span (ZMod 2) (Set.range (fun i : Fin 2 => b (Fin.castSucc i)))
  have hU2 : finrank (ZMod 2) U = 2 := by
    change finrank (ZMod 2) ↥(Submodule.span (ZMod 2)
      (Set.range ((⇑b) ∘ Fin.castSucc))) = 2
    rw [finrank_span_eq_card (b.linearIndependent.comp _ (Fin.castSucc_injective 2))]
    simp
  let inc : Vd →ₗ[ZMod 2] Vt S g D.t :=
    Vd.subtype.codRestrict (Vt S g D.t) fun x => x.2.2
  have hinc_inj : Function.Injective inc := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : Vt S g D.t => (x : S.Qt)) h
  let U' : Submodule (ZMod 2) (Vt S g D.t) := U.map inc
  have hU'2 : finrank (ZMod 2) U' = 2 := by
    rw [← (Submodule.equivMapOfInjective inc hinc_inj U).finrank_eq, hU2]
  obtain ⟨w, hwU', hwQ⟩ := hmin U' hU'2
  obtain ⟨uV, huVU, hu_eq⟩ := Submodule.mem_map.mp hwU'
  let u : Vt S g D.t := inc uV
  have hw_eq : w = u := hu_eq.symm
  subst w
  have huQ : Q u ≠ 0 := hwQ
  have hu0ne : u ≠ 0 := by
    intro h0
    rw [h0] at huQ
    simpa using huQ
  have hu0Q1 : Q u = 1 := by
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases h01 (Q u) with h | h
    · exact absurd h huQ
    · exact h
  have hu0Vd : (u : S.Qt) ∈ Vd := by
    change (uV : S.Qt) ∈ Vd
    exact uV.2
  have hu0clSub : (u : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := hu0Vd.1
  have hu0Vt : (u : S.Qt) ∈ Vt S g D.t := hu0Vd.2
  obtain ⟨x, hxX, -, hcl⟩ := S.mem_clSub_iff.mp hu0clSub
  have hcl' : S.cl x = (u : S.Qt) := hcl
  have hxV : S.cl x ∈ Vt S g D.t := by rwa [hcl']
  have hxsq : x ^ 2 = 1 := S.QG_inf_Qa_sq W.H.conj_ne hxX
  have hx1 : x ≠ 1 := by
    intro hx
    apply hu0ne
    apply Subtype.ext
    rw [← hcl', hx, S.cl_one]
    rfl
  have hxz : x ≠ S.z := by
    intro hx
    apply hu0ne
    apply Subtype.ext
    rw [← hcl', hx, S.cl_z]
    rfl
  have hclne : S.cl x ≠ S.cl (g * S.z * g⁻¹) := by
    intro h
    have hQa : Q (aV D.mem_Lbar) = 0 :=
      (hsing _ (aV_ne_zero W.H D.mem_Lbar)).mpr ⟨1, one_mem _, rfl⟩
    have h1 : Q u = 0 := by
      calc Q u = Q (⟨S.cl x, hxV⟩ : Vt S g D.t) :=
            congrArg Q (Subtype.ext hcl').symm
        _ = Q (aV D.mem_Lbar) := by
            apply congrArg Q
            exact Subtype.ext h
        _ = 0 := hQa
    rw [hu0Q1] at h1
    norm_num at h1
  have hQx : Q ⟨S.cl x, hxV⟩ = 1 :=
    (congrArg Q (Subtype.ext hcl')).trans hu0Q1
  have hnotX : ¬ ∃ ξ ∈ D.Xhat,
      (ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aV D.mem_Lbar) = S.cl x := by
    rintro ⟨ξ, hξ, hξa⟩
    have horb : (⟨S.cl x, hxV⟩ : Vt S g D.t) ∈
        orbitOf (RmodN S g D.t) (aV D.mem_Lbar) := by
      refine ⟨resV W.H.conj_mem D.t ⟨ξ, W.F.XR hξ⟩, ?_, ?_⟩
      · have hmem : resV W.H.conj_mem D.t ⟨ξ, W.F.XR hξ⟩ ∈
            imgR W.H.conj_mem D.t D.Xhat := ⟨⟨ξ, W.F.XR hξ⟩, hξ, rfl⟩
        rwa [W.hKR] at hmem
      · apply Subtype.ext
        rw [S4.coe_resV_apply]
        exact hξa
    have hzero := (hsing ⟨S.cl x, hxV⟩ (by
      intro h0
      have : Q ⟨S.cl x, hxV⟩ = 0 := by rw [h0]; simp
      rw [hQx] at this
      norm_num at this)).mpr horb
    rw [hQx] at hzero
    norm_num at hzero
  exact ⟨x, hxX, orderOf_eq_prime hxsq hx1, hxz, hclne, hxV, hQx, hnotX⟩



theorem SwapW4.mem_P_of_sq_mem (W : SwapW4 D) {n : D.Z}
    (hnN : n ∈ normalizer (SwapW4.P D W : Set D.Z))
    (hn2 : n ^ 2 ∈ SwapW4.P D W) : n ∈ SwapW4.P D W := by
  classical
  let P : Subgroup D.Z := SwapW4.P D W
  let N : Subgroup D.Z := normalizer (P : Set D.Z)
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hPcard : Nat.card P = 4 := SwapW4.card_P D W
  let Psub : Subgroup N := P.subgroupOf N
  have hPsub_card : Nat.card ↥Psub = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv]
    exact hPcard
  have hPp : IsPGroup 2 ↥Psub :=
    IsPGroup.of_card (n := 2) (by rw [hPsub_card]; norm_num)
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hPsub_le : Psub ≤ (S : Subgroup N) := hPS
  have hS_card_dvd : Nat.card ↥S ∣ Nat.card D.Z :=
    Subgroup.card_dvd_of_injective (N.subtype.comp (S : Subgroup N).subtype) (by
      intro a b h
      exact Subtype.ext (Subtype.ext h))
  have h4le : 4 ≤ Nat.card ↥S := by
    calc 4 = Nat.card ↥Psub := hPsub_card.symm
      _ ≤ Nat.card ↥S := Nat.card_le_card_of_injective
          (fun x : Psub => (⟨x.1, hPsub_le x.2⟩ : S))
          (fun a b h => Subtype.ext (congrArg (fun x : S => (x.1 : N)) h))
  have hS_card_le : Nat.card ↥S ≤ 4 := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hdvd : Nat.card ↥S ∣ 60 := by
      rw [← SwapW4.card_Z D W]
      exact hS_card_dvd
    have hkS : Nat.card ↥S = 2 ^ k := hk
    have h4le' : 4 ≤ 2 ^ k := by rw [← hkS]; exact h4le
    have hdvd' : 2 ^ k ∣ 60 := by rw [← hkS]; exact hdvd
    change Nat.card ↥(S : Subgroup N) ≤ 4
    rw [show Nat.card ↥(S : Subgroup N) = 2 ^ k from hk]
    have hk_ge : 2 ≤ k := by
      by_contra h
      have hk1 : k ≤ 1 := by omega
      interval_cases k <;> norm_num at h4le'
    have hk_le : k ≤ 5 := by
      have hle60 : 2 ^ k ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd'
      by_contra h
      have h6 : 6 ≤ k := by omega
      have h64 : 64 ≤ 2 ^ k := by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) h6
      omega
    interval_cases k <;> norm_num at hdvd'
    norm_num
  have hS_eq : (S : Subgroup N) = Psub := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hPsub_le
    rw [hPsub_card]
    exact hS_card_le
  have hPsub_normal : Psub.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr (le_refl N)
  have hSnorm : (S : Subgroup N).Normal := by
    rw [hS_eq]
    exact hPsub_normal
  let nN : N := ⟨n, hnN⟩
  have hn2Psub : (nN ^ 2) ∈ Psub := by
    change (n ^ 2 : D.Z) ∈ P
    exact hn2
  obtain ⟨k, hk⟩ := hPp ⟨nN ^ 2, hn2Psub⟩
  have hpow : nN ^ (2 ^ (k + 1)) = 1 := by
    have h := congrArg (fun x : Psub => (x.1 : N)) hk
    change (nN ^ 2) ^ (2 ^ k) = 1 at h
    have hexp : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ]
      ring
    calc nN ^ (2 ^ (k + 1)) = nN ^ (2 * 2 ^ k) := congrArg (fun e => nN ^ e) hexp
      _ = (nN ^ 2) ^ (2 ^ k) := pow_mul nN 2 (2 ^ k)
      _ = 1 := h
  have hnNmem : nN ∈ S :=
    CFSG.GroupTheory.mem_sylow_of_pow_eq_one hSnorm (k := k + 1) hpow
  exact hS_eq.le hnNmem



theorem SwapW4.e_inv_t_e_t_decomp (W : SwapW4 D) {e z1 z2 : S.O} (u : D.Z)
    (hu : (u : S.O) = z1⁻¹ * z2)
    (he : e = z1 * (D.t * z2 * D.t⁻¹))
    (hz1 : z1 ∈ D.Z) (hz2 : z2 ∈ D.Z) :
    e⁻¹ * D.t * e * D.t =
      (u : S.O) * (D.t * ((u⁻¹ : D.Z) : S.O) * D.t⁻¹) := by
  have ht2 : D.t * D.t = 1 := D.t_mul_t W.H
  have hti : D.t⁻¹ = D.t := D.t_inv W.H
  have hW1 : D.t * z1 * D.t⁻¹ ∈ D.W := D.conj_mem_W hz1
  have hW2 : D.t * z2⁻¹ * D.t⁻¹ ∈ D.W := D.conj_mem_W (D.Z.inv_mem hz2)
  have h21 : z1⁻¹ * (D.t * z2⁻¹ * D.t⁻¹) =
      (D.t * z2⁻¹ * D.t⁻¹) * z1⁻¹ :=
    (D.mul_comm_of_mem_W hW2 (D.Z.inv_mem hz1)).symm
  have h22 : z2 * (D.t * z2⁻¹ * D.t⁻¹) =
      (D.t * z2⁻¹ * D.t⁻¹) * z2 :=
    (D.mul_comm_of_mem_W hW2 hz2).symm
  have h12 : z2 * (D.t * z1 * D.t⁻¹) =
      (D.t * z1 * D.t⁻¹) * z2 :=
    (D.mul_comm_of_mem_W hW1 hz2).symm
  have hstep1 : (z1 * (D.t * z2 * D.t⁻¹))⁻¹ * D.t *
      (z1 * (D.t * z2 * D.t⁻¹)) * D.t =
      (D.t * z2⁻¹ * D.t⁻¹) * z1⁻¹ * (D.t * z1 * D.t⁻¹) * z2 := by
    simp [hti, ht2, mul_assoc]
  have hstep2 : (D.t * z2⁻¹ * D.t⁻¹) * z1⁻¹ * (D.t * z1 * D.t⁻¹) * z2 =
      z1⁻¹ * z2 * ((D.t * z2⁻¹ * D.t⁻¹) * (D.t * z1 * D.t⁻¹)) := by
    calc (D.t * z2⁻¹ * D.t⁻¹) * z1⁻¹ * (D.t * z1 * D.t⁻¹) * z2
        = z1⁻¹ * (D.t * z2⁻¹ * D.t⁻¹) * ((D.t * z1 * D.t⁻¹) * z2) := by
          rw [h21.symm]; group
      _ = z1⁻¹ * (D.t * z2⁻¹ * D.t⁻¹) * (z2 * (D.t * z1 * D.t⁻¹)) := by
          rw [h12.symm]
      _ = z1⁻¹ * ((D.t * z2⁻¹ * D.t⁻¹) * z2) * (D.t * z1 * D.t⁻¹) := by group
      _ = z1⁻¹ * (z2 * (D.t * z2⁻¹ * D.t⁻¹)) * (D.t * z1 * D.t⁻¹) := by
          rw [h22.symm]
      _ = z1⁻¹ * z2 * ((D.t * z2⁻¹ * D.t⁻¹) * (D.t * z1 * D.t⁻¹)) := by group
  have hstep3 : (D.t * z2⁻¹ * D.t⁻¹) * (D.t * z1 * D.t⁻¹) =
      D.t * (z2⁻¹ * z1) * D.t⁻¹ := by
    calc (D.t * z2⁻¹ * D.t⁻¹) * (D.t * z1 * D.t⁻¹)
        = D.t * z2⁻¹ * (D.t⁻¹ * D.t) * z1 * D.t⁻¹ := by group
      _ = D.t * z2⁻¹ * (D.t * D.t) * z1 * D.t := by rw [hti]
      _ = D.t * z2⁻¹ * z1 * D.t := by rw [ht2, mul_one]
      _ = D.t * (z2⁻¹ * z1) * D.t⁻¹ := by rw [hti]; group
  have hu_inv : ((u⁻¹ : D.Z) : S.O) = z2⁻¹ * z1 := by
    change ((u : S.O))⁻¹ = z2⁻¹ * z1
    rw [hu]
    group
  rw [he, hstep1, hstep2, hstep3, hu, hu_inv]



theorem SwapW4.not_mem_orb_E2 (W : SwapW4 D) {v : Vt S g D.t}
    (hv : ¬ ∃ ξ ∈ D.Xhat,
      (ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aV D.mem_Lbar) = (v : S.Qt)) :
    (v : S.Qt) ∉ SwapW4.orb (D.Z ⊔ D.W) (aV D.mem_Lbar) := by
  classical
  intro horb
  let E : Subgroup S.O := D.Z ⊔ D.W
  let a : S.Qt := aV D.mem_Lbar
  obtain ⟨e, he, hev⟩ := horb
  have htv : ((D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt) = (v : S.Qt) := by
    apply mem_fixSpace.mp
    rw [W.hFix]
    exact v.2
  have hta : ((D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := by
    apply mem_fixSpace.mp
    rw [W.hFix]
    exact (aV D.mem_Lbar).2
  have hev_inv : (((e : S.O)⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt) = a := by
    calc (((e : S.O)⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt)
        = (((e : S.O)⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) := by rw [hev]
      _ = a := by simp
  let q : S.O := e⁻¹ * D.t * e * D.t
  have hqfix : ((q : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := by
    change (((e : S.O)⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((((D.t : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((e : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((((D.t : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) a))) = a
    rw [hta, hev, htv, hev_inv]
  have htEt : D.t * e * D.t⁻¹ ∈ E := by
    obtain ⟨p0, hp0, -⟩ := SwapW4.decomp D W he
    obtain ⟨⟨z1, hz1⟩, ⟨z2, hz2⟩⟩ := p0
    change e = z1 * (D.t * z2 * D.t⁻¹) at hp0
    have hprod : D.t * e * D.t⁻¹ = (D.t * z1 * D.t⁻¹) * z2 := by
      rw [hp0, D.t_inv W.H]
      calc D.t * (z1 * (D.t * z2 * D.t)) * D.t
          = D.t * z1 * D.t * z2 * (D.t * D.t) := by group
        _ = D.t * z1 * D.t * z2 := by rw [D.t_mul_t W.H, mul_one]
    rw [hprod]
    exact (by
      have hmem : (D.t * z1 * D.t⁻¹) * z2 ∈ D.W ⊔ D.Z :=
        Subgroup.mul_mem_sup (D.conj_mem_W hz1) hz2
      simpa [E, sup_comm] using hmem)
  have hqE : q ∈ E := by
    have hq_eq : q = e⁻¹ * (D.t * e * D.t⁻¹) := by
      change e⁻¹ * D.t * e * D.t = e⁻¹ * (D.t * e * D.t⁻¹)
      rw [D.t_inv W.H]
      group
    rw [hq_eq]
    exact E.mul_mem (E.inv_mem he) htEt
  have hqN : q ∈ normalizer (S.Lbar g : Set S.O) :=
    SwapW4.stabilizer_a_le_normalizer D W
      ⟨hqE, (SwapW4.mem_stab (v := a) (e := q)).mpr hqfix⟩
  obtain ⟨p, hpP, n, hnN, hq_eq⟩ :=
    SwapW4.normalizer_E2_subset D W hqE hqN
  obtain ⟨p0, hp0, -⟩ := SwapW4.decomp D W he
  obtain ⟨⟨z1, hz1⟩, ⟨z2, hz2⟩⟩ := p0
  change e = z1 * (D.t * z2 * D.t⁻¹) at hp0
  let u : D.Z := ⟨z1⁻¹ * z2, D.Z.mul_mem (D.Z.inv_mem hz1) hz2⟩
  have hu : (u : S.O) = z1⁻¹ * z2 := rfl
  have hq_formula : q = (u : S.O) * (D.t * ((u⁻¹ : D.Z) : S.O) * D.t⁻¹) := by
    exact SwapW4.e_inv_t_e_t_decomp D W u hu hp0 hz1 hz2
  have hq_L7 : q = ((p * n : D.Z) : S.O) * (D.t * (n : S.O) * D.t⁻¹) := by
    rw [hq_eq, S5.SwapData.chi_apply]
    change (p : S.O) * ((n : S.O) * (D.t * (n : S.O) * D.t⁻¹)) =
      ((p * n : D.Z) : S.O) * (D.t * (n : S.O) * D.t⁻¹)
    rw [Subgroup.coe_mul]
    group
  have huniqQ := (SwapW4.decomp D W hqE).choose_spec.2
  have hpair1 := huniqQ (u, u⁻¹) hq_formula
  have hpair2 := huniqQ (⟨p * n, D.Z.mul_mem p.2 n.2⟩, n) hq_L7
  have hpair := hpair1.trans hpair2.symm
  have hpn : p * n = u :=
    (congrArg (fun q : D.Z × D.Z => (q.1 : D.Z)) hpair).symm
  have hn_eq : n = u⁻¹ :=
    (congrArg (fun q : D.Z × D.Z => (q.2 : D.Z)) hpair).symm
  have hn2 : n ^ 2 = p⁻¹ := by
    have hpu : p * u⁻¹ = u := by
      simpa [hn_eq] using hpn
    have hp : p = u * u := by
      calc p = (p * u⁻¹) * u := by group
        _ = u * u := by rw [hpu]
    calc n ^ 2 = (u⁻¹) ^ 2 := by rw [hn_eq]
      _ = p⁻¹ := by rw [hp]; group
  have hn2P : n ^ 2 ∈ SwapW4.P D W := by
    rw [hn2]
    exact (SwapW4.P D W).inv_mem hpP
  have hnP : n ∈ SwapW4.P D W := SwapW4.mem_P_of_sq_mem D W hnN hn2P
  have hn_val : (n : S.O) = z2⁻¹ * z1 := by
    calc (n : S.O) = ((u⁻¹ : D.Z) : S.O) := by rw [hn_eq]
      _ = ((u : S.O))⁻¹ := rfl
      _ = z2⁻¹ * z1 := by rw [hu]; group
  have hz1eq : z1 = z2 * (n : S.O) := by
    calc z1 = z2 * (z2⁻¹ * z1) := by group
      _ = z2 * (n : S.O) := by rw [← hn_val]
  have he_eq : e = (D.chi ⟨z2, hz2⟩ : S.O) * (n : S.O) := by
    rw [hp0, S5.SwapData.chi_apply, hz1eq]
    have hnW : (n : S.O) * (D.t * z2 * D.t⁻¹) =
        (D.t * z2 * D.t⁻¹) * (n : S.O) :=
      D.mul_comm_of_mem n.2 (D.conj_mem_W hz2)
    calc (z2 * (n : S.O)) * (D.t * z2 * D.t⁻¹)
        = z2 * ((n : S.O) * (D.t * z2 * D.t⁻¹)) := by group
      _ = z2 * ((D.t * z2 * D.t⁻¹) * (n : S.O)) := by rw [hnW]
      _ = (z2 * (D.t * z2 * D.t⁻¹)) * (n : S.O) := by group
  have hna : ((n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := by
    change ((n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹)
    exact SwapW4.fix_a_of_mem_P D W hnP
  have hva : (((D.chi ⟨z2, hz2⟩ : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = (v : S.Qt) := by
    calc (((D.chi ⟨z2, hz2⟩ : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) a
        = (((D.chi ⟨z2, hz2⟩ : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) := by rw [hna]
      _ = ((((D.chi ⟨z2, hz2⟩ : S.O) * (n : S.O)) : S.O) :
            S.Qt ≃ₗ[ZMod 2] S.Qt) a := by rfl
      _ = ((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by rw [← he_eq]
      _ = (v : S.Qt) := hev
  exact hv ⟨D.chi ⟨z2, hz2⟩, D.chi_mem_Xhat ⟨z2, hz2⟩, hva⟩



theorem SwapW4.card_K_ge_of_ne (W : SwapW4 D) {x : G}
    (hxX : x ∈ S.QG ⊓ S.Qa g)
    (hxV : S.cl x ∈ Vt S g D.t)
    (hxne : S.cl x ≠ 0)
    (hnotX : ¬ ∃ ξ ∈ D.Xhat,
      (ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aV D.mem_Lbar) = S.cl x)
    (K : Subgroup S.O)
    (hK : ∀ m : S.O, m ∈ K ↔ m ∈ D.Z ⊔ D.W ∧
      (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x) :
    60 ≤ Nat.card K := by
  classical
  let E : Subgroup S.O := D.Z ⊔ D.W
  let a : S.Qt := aV D.mem_Lbar
  let xv : S.Qt := S.cl x
  have hqa : S.q a = 0 := by
    change S.q (S.cl (g * S.z * g⁻¹)) = 0
    exact S.q_cl_conj_z W.H.conj_mem
  have hqx : S.q xv = 0 := by
    change S.q (S.cl x) = 0
    exact (S.q_cl_eq_zero_iff hxX.1).mpr (S.QG_inf_Qa_sq W.H.conj_ne hxX)
  let Sing : Set S.Qt := {v | S.q v = 0}
  let Nsing : Set S.Qt := {v | S.q v = 0 ∧ v ≠ 0}
  have hSing : Sing.ncard = 136 := by
    have h := W4As.card_singular_eq_136 (V := S.Qt) S.q_nondegenerate
      (by rw [S.finrank_Qt_eq_two_mul_width, W.hw])
      (by
        rw [S4.finrank_clSub_QG_inf_Qa W.H.conj_mem W.H.conj_ne W.C.card_QG_inf_Qa,
          W.hw])
      (fun v hv => S.q_eq_zero_of_mem_clSub_QG_inf_Qa W.H.conj_ne hv)
    have h' : Nat.card ↥Sing = 136 := h
    rwa [Nat.card_coe_set_eq] at h'
  have hNcard : Nsing.ncard = 135 := by
    have h0 : (0 : S.Qt) ∈ Sing := by simp [Sing]
    have hdiff : Nsing = Sing \ {0} := by
      ext v
      change (S.q v = 0 ∧ v ≠ 0) ↔
        (S.q v = 0 ∧ v ∉ ({0} : Set S.Qt))
      simp only [Set.mem_singleton_iff]
    rw [hdiff]
    have h := Set.ncard_diff_singleton_add_one h0
    omega
  have hsub_a : SwapW4.orb E a ⊆ Nsing := by
    rintro y ⟨e, he, rfl⟩
    refine ⟨?_, ?_⟩
    · calc S.q (((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) = S.q a :=
            TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (e : S.O).2 a
        _ = 0 := hqa
    · intro h0
      have h := congrArg (((e : S.O)⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt) h0
      simpa [a, aV_ne_zero W.H D.mem_Lbar] using h
  have hsub_x : SwapW4.orb E xv ⊆ Nsing := by
    rintro y ⟨e, he, rfl⟩
    refine ⟨?_, ?_⟩
    · calc S.q (((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) xv) = S.q xv :=
            TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (e : S.O).2 xv
        _ = 0 := hqx
    · intro h0
      have h := congrArg (((e : S.O)⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt) h0
      exact hxne (by simpa using h)
  have hdisj : Disjoint (SwapW4.orb E a) (SwapW4.orb E xv) := by
    rw [Set.disjoint_left]
    intro y hya hyx
    have hxorb : xv ∈ SwapW4.orb E a := by
      obtain ⟨e1, he1, rfl⟩ := hya
      obtain ⟨e2, he2, h2⟩ := hyx
      refine ⟨e2⁻¹ * e1, E.mul_mem (E.inv_mem he2) he1, ?_⟩
      calc ((e2⁻¹ * e1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a
          = (((e2 : S.O)⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt)
              (((e1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) := rfl
        _ = (((e2 : S.O)⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt)
              (((e2 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) xv) := by rw [h2]
        _ = xv := by simp
    exact (SwapW4.not_mem_orb_E2 D W (v := ⟨S.cl x, hxV⟩) hnotX) hxorb
  have hunion_sub : SwapW4.orb E a ∪ SwapW4.orb E xv ⊆ Nsing :=
    Set.union_subset hsub_a hsub_x
  have hunion_le : (SwapW4.orb E a ∪ SwapW4.orb E xv).ncard ≤ Nsing.ncard :=
    Set.ncard_le_ncard hunion_sub
  have hunion_card : (SwapW4.orb E a ∪ SwapW4.orb E xv).ncard =
      (SwapW4.orb E a).ncard + (SwapW4.orb E xv).ncard :=
    Set.ncard_union_eq hdisj
  have ha_card : 75 ≤ (SwapW4.orb E a).ncard := by
    have h := SwapW4.card_orbit_a D W
    simpa [E, a, Nat.card_coe_set_eq] using h
  have hx_card : (SwapW4.orb E xv).ncard ≤ 60 := by omega
  letI : MulAction ↥E S.Qt :=
    MulAction.compHom (M := S.O) (N := ↥E) S.Qt (Subgroup.subtype E)
  let Sx : Subgroup ↥E := MulAction.stabilizer ↥E xv
  have horb_x_eq : SwapW4.orb E xv = MulAction.orbit ↥E xv := by
    ext y
    change (∃ e ∈ E, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) xv = y) ↔
      (∃ g : ↥E, g • xv = y)
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, g.2, rfl⟩
  have horb_index : (SwapW4.orb E xv).ncard = Sx.index := by
    calc (SwapW4.orb E xv).ncard = Nat.card ↥(SwapW4.orb E xv) :=
          (Nat.card_coe_set_eq _).symm
      _ = Nat.card ↥(MulAction.orbit ↥E xv) := by rw [horb_x_eq]
      _ = Nat.card (↥E ⧸ Sx) :=
          Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥E xv)
      _ = Sx.index := (Subgroup.index_eq_card _).symm
  have hindex_le : Sx.index ≤ 60 := by
    rwa [← horb_index]
  have hK_eq : K = E ⊓ SwapW4.stab xv := by
    ext m
    rw [hK m, Subgroup.mem_inf, SwapW4.mem_stab]
  have hstab_sub : Sx = (E ⊓ SwapW4.stab xv).subgroupOf E := by
    ext m
    rw [MulAction.mem_stabilizer_iff]
    change ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) xv = xv ↔
      (m : S.O) ∈ E ⊓ SwapW4.stab xv
    constructor
    · intro h
      exact ⟨m.2, h⟩
    · rintro ⟨-, h⟩
      exact h
  have hKcard : Nat.card K = Nat.card Sx := by
    rw [hK_eq, hstab_sub]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ SwapW4.stab xv ≤ E)).toEquiv).symm
  have hOS : Sx.index * Nat.card Sx = Nat.card ↥E := Subgroup.index_mul_card Sx
  have hcardE : Nat.card ↥E = 3600 := SwapW4.card_E2 D W
  rw [hcardE] at hOS
  by_contra hlt
  push Not at hlt
  have hSxle : Nat.card Sx ≤ 59 := by omega
  have hle : Sx.index * Nat.card Sx ≤ 60 * 59 := Nat.mul_le_mul hindex_le hSxle
  omega



theorem SwapW4.card_K_ge (W : SwapW4 D) {x : G}
    (hxX : x ∈ S.QG ⊓ S.Qa g)
    (hxV : S.cl x ∈ Vt S g D.t)
    (hnotX : ¬ ∃ ξ ∈ D.Xhat,
      (ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aV D.mem_Lbar) = S.cl x)
    (K : Subgroup S.O)
    (hK : ∀ m : S.O, m ∈ K ↔ m ∈ D.Z ⊔ D.W ∧
      (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x) :
    60 ≤ Nat.card K := by
  classical
  let E : Subgroup S.O := D.Z ⊔ D.W
  let xv : S.Qt := S.cl x
  by_cases hx0 : xv = 0
  · have hx0' : S.cl x = 0 := hx0
    have hK_eq_E : K = E := by
      ext m
      rw [hK m, hx0']
      simp [E]
    rw [hK_eq_E]
    have hE : Nat.card ↥E = 3600 := SwapW4.card_E2 D W
    omega
  · exact SwapW4.card_K_ge_of_ne D W hxX hxV hx0 hnotX K hK


end CFSG.GF2Type.Smith1979.W4Swap
