module

public import CFSG.GH74.GLS.SP.Local.SPLOrdG5
public import CFSG.GH74.GLS.SP.Local.SPLOrdOut
public import CFSG.GH74.GLS.SP.Local.SPLOrdG3

public section

open Subgroup DihedralGroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section G6

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

@[expose] def SPLNot3.Chat (D : SPLNot3 G) : Subgroup G := D.I ⊔ D.A ⊔ zpowers D.x ⊔ zpowers D.z

omit [Finite G] in
theorem Ct_le_normalizer_I (hc : SPL2Ct D.toSPLNot2) : D.Ct ≤ normalizer (D.I : Set G) := by
  intro c hc'
  rw [mem_normalizer_iff]
  intro i
  constructor
  · intro hi; exact I_normalized D hc c hc' i hi
  · intro hi
    have := I_normalized D hc c⁻¹ (D.Ct.inv_mem hc') _ hi
    have e : c⁻¹ * (c * i * c⁻¹) * c⁻¹⁻¹ = i := by group
    rwa [e] at this

@[expose] noncomputable def ctAct (hc : SPL2Ct D.toSPLNot2) : ↥D.Ct →* MulAut ↥D.I :=
  D.I.normalizerMonoidHom.comp (Subgroup.inclusion (Ct_le_normalizer_I D hc))

omit [Finite G] in
theorem ctAct_apply (hc : SPL2Ct D.toSPLNot2) (c : ↥D.Ct) (i : ↥D.I) :
    (((ctAct D hc c) i : ↥D.I) : G) = (c : G) * i * (c : G)⁻¹ := rfl

@[expose] noncomputable def sigmaAut (hc : SPL2Ct D.toSPLNot2) : MulAut ↥D.I :=
  ctAct D hc ⟨D.x, x_mem_Ct D hc⟩

omit [Finite G] in
theorem sigmaAut_apply (hc : SPL2Ct D.toSPLNot2) (i : ↥D.I) :
    ((sigmaAut D hc i : ↥D.I) : G) = D.x * i * D.x⁻¹ := rfl

omit [Finite G] in
theorem sigmaAut_sq (hc : SPL2Ct D.toSPLNot2) : sigmaAut D hc * sigmaAut D hc = 1 := by
  apply MulEquiv.ext
  intro i
  apply Subtype.ext
  show ((sigmaAut D hc (sigmaAut D hc i) : ↥D.I) : G) = i
  rw [sigmaAut_apply, sigmaAut_apply]
  have h := hc.x2_cen (i : G) (Subgroup.mem_sup_left i.2)
  rw [pow_two] at h
  calc D.x * (D.x * i * D.x⁻¹) * D.x⁻¹ = (D.x * D.x) * i * (D.x * D.x)⁻¹ := by group
    _ = i := by rw [h]; group

omit [Finite G] in
theorem x_mem_Chat : D.x ∈ D.Chat :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers _))

omit [Finite G] in
theorem z_mem_Chat : D.z ∈ D.Chat := Subgroup.mem_sup_right (mem_zpowers _)

omit [Finite G] in
theorem I_le_Chat : D.I ≤ D.Chat := fun _ h =>
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left h))

omit [Finite G] in
theorem A_le_Chat : D.A ≤ D.Chat := fun _ h =>
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right h))

theorem Chat_le_Ct (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) : D.Chat ≤ D.Ct := by
  refine sup_le (sup_le (sup_le (I_le_Ct D hc) (A_le_Ct D hc)) ?_) ?_
  · rw [zpowers_le]; exact x_mem_Ct D hc
  · rw [zpowers_le]; exact z_mem_Ct D hs

omit [Finite G] in
theorem cen_le_Chat (hc : SPL2Ct D.toSPLNot2) {u : G} (hu : u ∈ D.Ct)
    (hcen : ∀ i ∈ D.I, u * i = i * u) : u ∈ D.Chat := by
  have h1 : u ∈ centralizer (D.I : Set G) := by
    rw [mem_centralizer_iff]; intro i hi; exact (hcen i hi).symm
  have h : u ∈ centralizer (D.I : Set G) ⊓ D.Ct := ⟨h1, hu⟩
  rw [hc.cen_I] at h
  have hle : D.A ⊔ (zpowers (D.x ^ 2) ⊔ zpowers D.z) ≤ D.Chat := by
    refine sup_le (A_le_Chat D) (sup_le ?_ ?_)
    · rw [zpowers_le]; exact Subgroup.pow_mem _ (x_mem_Chat D) 2
    · rw [zpowers_le]; exact z_mem_Chat D
  exact hle h

theorem F_normalizes_Chat (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    ∀ f ∈ D.F, ∀ c ∈ D.Chat, f * c * f⁻¹ ∈ D.Chat := by
  intro f hf c hcC
  obtain ⟨F₁, hFfield, hFfin, hqF, ⟨e⟩⟩ := hc.I_L2
  have hL : CFSG.GH74.GLS.IVK.L2Field F₁ :=
    ⟨by rw [hqF]; exact hs.odd_q, by rw [hqF]; have := hs.q_ge; omega⟩
  have hfCt : f ∈ D.Ct := hc.F_eq hf
  have hxCt : D.x ∈ D.Ct := x_mem_Ct D hc
  have hzCt : D.z ∈ D.Ct := z_mem_Ct D hs
  let fC : ↥D.Ct := ⟨f, hfCt⟩
  let xC : ↥D.Ct := ⟨D.x, hxCt⟩
  let zC : ↥D.Ct := ⟨D.z, hzCt⟩
  have hx_case : f * D.x * f⁻¹ ∈ D.Chat := by
    obtain ⟨j, hj⟩ := out_abelian hL e (ctAct D hc fC) (sigmaAut D hc)
    let cc : ↥D.Ct := fC * xC * fC⁻¹ * xC⁻¹
    have hact : ctAct D hc cc = ⁅ctAct D hc fC, sigmaAut D hc⁆ := by
      show ctAct D hc (fC * xC * fC⁻¹ * xC⁻¹) = _
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      rfl
    have hcc : (cc : G) = f * D.x * f⁻¹ * D.x⁻¹ := rfl
    have hjI : ∀ i : ↥D.I, (cc : G) * i * (cc : G)⁻¹ = (j : G) * i * (j : G)⁻¹ := by
      intro i
      rw [← ctAct_apply D hc cc i, hact, ← hj]
      rfl
    have hjCt : (j : G) ∈ D.Ct := I_le_Ct D hc j.2
    have hu : (j : G)⁻¹ * (cc : G) ∈ D.Chat := by
      refine cen_le_Chat D hc (Subgroup.mul_mem _ (D.Ct.inv_mem hjCt) cc.2) ?_
      intro i hi
      have h1 := hjI ⟨i, hi⟩
      calc ((j : G)⁻¹ * (cc : G)) * i = (j : G)⁻¹ * ((cc : G) * i * (cc : G)⁻¹) * (cc : G) := by group
        _ = (j : G)⁻¹ * ((j : G) * i * (j : G)⁻¹) * (cc : G) := by rw [h1]
        _ = (i : G) * ((j : G)⁻¹ * (cc : G)) := by group
    have hcc' : (cc : G) = (j : G) * ((j : G)⁻¹ * (cc : G)) := by group
    have hccC : (cc : G) ∈ D.Chat := by
      rw [hcc']
      exact Subgroup.mul_mem _ (I_le_Chat D j.2) hu
    have : f * D.x * f⁻¹ = (cc : G) * D.x := by rw [hcc]; group
    rw [this]
    exact Subgroup.mul_mem _ hccC (x_mem_Chat D)
  have hz_case : f * D.z * f⁻¹ ∈ D.Chat := by
    let cc : ↥D.Ct := fC * zC * fC⁻¹ * zC⁻¹
    have hzact : ctAct D hc zC = 1 := by
      apply MulEquiv.ext
      intro i
      apply Subtype.ext
      show D.z * (i : G) * D.z⁻¹ = (i : G)
      have := z_cen_I D hs hc i i.2
      calc D.z * (i : G) * D.z⁻¹ = (i : G) * D.z * D.z⁻¹ := by rw [this]
        _ = i := by group
    have hact : ctAct D hc cc = 1 := by
      show ctAct D hc (fC * zC * fC⁻¹ * zC⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hzact]
      simp
    have hcc : (cc : G) = f * D.z * f⁻¹ * D.z⁻¹ := rfl
    have hccC : (cc : G) ∈ D.Chat := by
      refine cen_le_Chat D hc cc.2 ?_
      intro i hi
      have h1 := ctAct_apply D hc cc ⟨i, hi⟩
      rw [hact] at h1
      have h2 : (i : G) = (cc : G) * i * (cc : G)⁻¹ := h1
      calc (cc : G) * i = ((cc : G) * i * (cc : G)⁻¹) * (cc : G) := by group
        _ = (i : G) * (cc : G) := by rw [← h2]
    have : f * D.z * f⁻¹ = (cc : G) * D.z := by rw [hcc]; group
    rw [this]
    exact Subgroup.mul_mem _ hccC (z_mem_Chat D)
  have hgen : D.Chat ≤ D.Chat.comap (MulAut.conj f).toMonoidHom := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · intro i hi
      show f * i * f⁻¹ ∈ D.Chat
      exact I_le_Chat D (I_normalized D hc f hfCt i hi)
    · intro a ha
      show f * a * f⁻¹ ∈ D.Chat
      exact A_le_Chat D (A_norm_Ct D hc f hfCt a ha)
    · rw [zpowers_le]; exact hx_case
    · rw [zpowers_le]; exact hz_case
  exact hgen hcC

theorem F_le_normalizer_Chat (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    D.F ≤ normalizer (D.Chat : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact F_normalizes_Chat D hs hc y hy x hx
  · intro hx
    have := F_normalizes_Chat D hs hc y⁻¹ (D.F.inv_mem hy) _ hx
    have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
    rwa [e] at this

omit [Finite G] in
theorem Ct_eq_Chat_sup_F (hc : SPL2Ct D.toSPLNot2) : D.Ct = D.Chat ⊔ D.F := by
  have h := hc.Ct_eq
  have hF₀ : D.F₀ = D.F := inf_eq_left.mpr hc.F_eq
  have h' : D.Ct = D.I ⊔ D.A ⊔ D.F ⊔ zpowers D.x ⊔ zpowers D.z := by
    rw [← hF₀]; exact h
  rw [h']
  unfold SPLNot3.Chat
  ac_rfl

omit [Finite G] in
theorem dvd_two_d (hs : SPLSetup D.toSPLNot0) : 2 ∣ D.d :=
  dvd_trans (by norm_num : 2 ∣ 4) (four_dvd_d D.toSPLNot0 hs.odd_q)

omit [Finite G] in
theorem neZero_d (hs : SPLSetup D.toSPLNot0) : NeZero D.d := ⟨by have := d_pos D hs; omega⟩

theorem I_inf_Dt (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) [NeZero D.d]
    (hd : 2 ∣ D.d) {g₀ : G} (hg₀ord : orderOf g₀ = D.d) (hzg : D.z ∉ zpowers g₀)
    (hzrel : D.z * g₀ * D.z⁻¹ = g₀⁻¹)
    (hgI : ∀ i : ↥D.I, g₀ * (i : G) * g₀⁻¹ = ((sigmaAut D hc i : ↥D.I) : G)) :
    D.I ⊓ (zpowers g₀ ⊔ zpowers D.z) = ⊥ := by
  have hz2 : D.z ^ 2 = 1 := by rw [pow_two]; exact z_mul_z D hs
  have hd4 := d_pos D hs
  obtain ⟨ψ, hψinj, hψr, hψsr, hψrange⟩ :=
    exists_dih_embedding (by omega : 2 ≤ D.d) hg₀ord hzg hz2 hzrel
  have hact := dih_conj_action D.I hd ψ hψr hψsr (sigmaAut D hc) (sigmaAut_sq D hc) hgI
    (fun i hi => by
      have := z_cen_I D hs hc i hi
      calc D.z * i * D.z⁻¹ = i * D.z * D.z⁻¹ := by rw [this]
        _ = i := by group)
  rw [eq_bot_iff]
  rintro w ⟨hwI, hwD⟩
  rw [← hψrange] at hwD
  obtain ⟨ρ, rfl⟩ := hwD
  rcases dihAct_cases (sigmaAut D hc) (sigmaAut_sq D hc) hd ρ with h1 | h1
  · have hcomm : ∀ i : ↥D.I, (⟨ψ ρ, hwI⟩ : ↥D.I) * i = i * ⟨ψ ρ, hwI⟩ := by
      intro i
      apply Subtype.ext
      have h2 := hact ρ i
      rw [h1] at h2
      have h3 : ψ ρ * (i : G) * (ψ ρ)⁻¹ = i := h2
      show ψ ρ * (i : G) = (i : G) * ψ ρ
      calc ψ ρ * (i : G) = (ψ ρ * (i : G) * (ψ ρ)⁻¹) * ψ ρ := by group
        _ = (i : G) * ψ ρ := by rw [h3]
    have := center_I_trivial D hc _ hcomm
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    refine sigma_not_inner D hs hc ⟨ψ ρ, hwI, fun i hi => ?_⟩
    have h2 := hact ρ ⟨i, hi⟩
    rw [h1] at h2
    rw [← sigmaAut_apply D hc ⟨i, hi⟩]
    exact h2.symm

theorem chat_iso (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) [NeZero D.d]
    (hd : 2 ∣ D.d) :
    ∃ g₀ : G, D.z * g₀ * D.z⁻¹ = g₀⁻¹ ∧ g₀ ^ (D.d / 2) = D.t ∧
      ∃ Φ : (↥D.I ⋊[dihAct (sigmaAut D hc) (sigmaAut_sq D hc) hd] DihedralGroup D.d) ≃* ↥D.Chat,
        (∀ (i : ↥D.I) (k : ZMod D.d), (Φ ⟨i, r k⟩ : G) = i * g₀ ^ k.val) ∧
        ∀ (i : ↥D.I) (k : ZMod D.d), (Φ ⟨i, sr k⟩ : G) = i * (D.z * g₀ ^ k.val) := by
  obtain ⟨g₀, hgen, hord, hzrel, ht, hgx, hzg, -⟩ := exists_g0 D hs hc
  have hd4 := d_pos D hs
  have hz2 : D.z ^ 2 = 1 := by rw [pow_two]; exact z_mul_z D hs
  have hgI : ∀ i : ↥D.I, g₀ * (i : G) * g₀⁻¹ = ((sigmaAut D hc i : ↥D.I) : G) := fun i => by
    rw [sigmaAut_apply]; exact hgx i i.2
  have hIinf := I_inf_Dt D hs hc hd hord hzg hzrel hgI
  obtain ⟨Φ, hΦr, hΦsr⟩ := exists_semidirect_iso D.I hd (by omega : 2 ≤ D.d) hord hzg hz2 hzrel
    (sigmaAut D hc) (sigmaAut_sq D hc) hgI
    (fun i hi => by
      have := z_cen_I D hs hc i hi
      calc D.z * i * D.z⁻¹ = i * D.z * D.z⁻¹ := by rw [this]
        _ = i := by group) hIinf
  have heq : D.I ⊔ (zpowers g₀ ⊔ zpowers D.z) = D.Chat := by
    rw [hgen]
    unfold SPLNot3.Chat
    ac_rfl
  refine ⟨g₀, hzrel, ht, Φ.trans (MulEquiv.subgroupCongr heq), ?_, ?_⟩
  · intro i k
    exact hΦr i k
  · intro i k
    exact hΦsr i k

theorem F_inf_Chat (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) : D.F ⊓ D.Chat = ⊥ := by
  have : NeZero D.d := neZero_d D hs
  have hd : 2 ∣ D.d := dvd_two_d D hs
  obtain ⟨g₀, hzrel, ht, Φ, hΦr, hΦsr⟩ := chat_iso D hs hc hd
  rw [eq_bot_iff]
  rintro f ⟨hfF, hfC⟩
  set a := Φ.symm ⟨f, hfC⟩ with ha
  have hfa : Φ a = ⟨f, hfC⟩ := by rw [ha]; simp
  have hfa' : (Φ a : G) = f := by rw [hfa]
  have hord : orderOf a = orderOf f := by
    rw [← MulEquiv.orderOf_eq Φ a, hfa]
    exact Subgroup.orderOf_mk f hfC
  have hodd : Odd (orderOf a) := by rw [hord]; exact F_odd D.toSPLNot0 hfF
  have hzC : D.z ∈ D.Chat := z_mem_Chat D
  have hzΦ : Φ ⟨1, sr 0⟩ = ⟨D.z, hzC⟩ := by
    apply Subtype.ext
    have := hΦsr 1 0
    rw [this]
    simp
  have hfz : f * D.z = D.z * f := mem_centralizer_singleton_iff.mp (F_le_C hs hfF)
  have hcomm : (⟨1, sr 0⟩ : ↥D.I ⋊[dihAct (sigmaAut D hc) (sigmaAut_sq D hc) hd] DihedralGroup D.d) * a =
      a * ⟨1, sr 0⟩ := by
    apply Φ.injective
    rw [map_mul, map_mul, hzΦ, hfa]
    apply Subtype.ext
    show D.z * f = f * D.z
    exact hfz.symm
  have hcomm' : sr 0 * a.right = a.right * sr 0 := congrArg SemidirectProduct.right hcomm
  have hdvd : orderOf a.right ∣ orderOf a := by
    have := orderOf_map_dvd (SemidirectProduct.rightHom (N := ↥D.I) (G := DihedralGroup D.d)
      (φ := dihAct (sigmaAut D hc) (sigmaAut_sq D hc) hd)) a
    simpa using this
  have hrodd : Odd (orderOf a.right) := hodd.of_dvd_nat hdvd
  have hright : a.right = 1 := by
    rcases hr : a.right with k | k
    · rw [hr] at hcomm' hrodd
      rw [sr_mul_r, r_mul_sr] at hcomm'
      have hk : k + k = 0 := by
        have h1 : (0 : ZMod D.d) + k = 0 - k := by
          have := sr.inj hcomm'
          exact this
        calc k + k = (0 + k) - (0 - k) := by ring
          _ = 0 := by rw [h1]; ring
      have hsq : (r k : DihedralGroup D.d) ^ 2 = 1 := by
        rw [pow_two, r_mul_r, hk]; rfl
      have h2 : orderOf (r k : DihedralGroup D.d) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      have h3 : orderOf (r k : DihedralGroup D.d) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact h
        · rw [h] at hrodd; exact absurd hrodd (by decide)
      exact orderOf_eq_one_iff.mp h3
    · rw [hr] at hrodd
      rw [orderOf_sr] at hrodd
      exact absurd hrodd (by decide)
  have hlast : (Φ a : G) = (a.left : G) := by
    have h1 : a = ⟨a.left, r 0⟩ := by
      refine SemidirectProduct.ext ?_ ?_
      · rfl
      · show a.right = r 0
        rw [hright]; rfl
    rw [h1, hΦr a.left 0]
    simp
  have hfI : f ∈ D.I := by rw [← hfa', hlast]; exact a.left.2
  have hfK : f ∈ D.F ⊓ D.K := ⟨hfF, I_le_K D hc hfI⟩
  rw [F_inf_K_eq (D := D.toSPLNot0) hs] at hfK
  exact hfK

theorem inv_Ct_le_Chat (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {c : G}
    (hcC : c ∈ D.Ct) (hc2 : c * c = 1) : c ∈ D.Chat := by
  have hF := F_le_normalizer_Chat D hs hc
  rw [Ct_eq_Chat_sup_F D hc] at hcC
  obtain ⟨k, hk, y, hyF, rfl⟩ := mem_sup_of_le_normalizer hF hcC
  have hy2 : y * y ∈ D.Chat := by
    have e : y * y = (k * (y * k * y⁻¹))⁻¹ := by
      have h' : k * (y * k * y⁻¹) * (y * y) = 1 := by
        calc k * (y * k * y⁻¹) * (y * y) = (k * y) * (k * y) := by group
          _ = 1 := hc2
      exact (eq_inv_of_mul_eq_one_right h')
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hk (F_normalizes_Chat D hs hc y hyF _ hk))
  have hy2F : y * y ∈ D.F := Subgroup.mul_mem _ hyF hyF
  have hy2one : y * y = 1 := by
    have : y * y ∈ D.F ⊓ D.Chat := ⟨hy2F, hy2⟩
    rw [F_inf_Chat D hs hc] at this
    exact Subgroup.mem_bot.mp this
  have hy1 : y = 1 := by
    have hodd := F_odd D.toSPLNot0 hyF
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2one)
    have : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp this
  rw [hy1, mul_one]
  exact hk

theorem card_Chat (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card ↥D.Chat = Nat.card ↥D.I * (2 * D.d) := by
  have : NeZero D.d := neZero_d D hs
  obtain ⟨g₀, -, -, Φ, -, -⟩ := chat_iso D hs hc (dvd_two_d D hs)
  rw [← Nat.card_congr Φ.toEquiv, SemidirectProduct.card, DihedralGroup.nat_card]

theorem card_Ct (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card ↥D.Ct = Nat.card ↥D.I * (2 * D.d) * Nat.card ↥D.F := by
  have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer (F_le_normalizer_Chat D hs hc)
  rw [inf_comm, F_inf_Chat D hs hc, Subgroup.card_bot, mul_one] at h
  rw [Ct_eq_Chat_sup_F D hc, h, card_Chat D hs hc]

end G6

end CFSG.GH74.GLS.SP.Local
