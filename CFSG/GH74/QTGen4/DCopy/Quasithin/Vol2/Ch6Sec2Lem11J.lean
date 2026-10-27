module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11J
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem11H

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem stage_e_ch611_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6210 : Stmt6_2_10_F4) (hG31 : Ch6G31O2)
    (h4 : (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V ≠ 2) :
    (∀ u ∈ uCh611 T L V, u ^ 2 = 1) ∧
      (∀ a ∈ uCh611 T L V, ∀ b ∈ uCh611 T L V, a * b = b * a) ∧
      Nat.card (uCh611 T L V) = 16 ∧
      uCh611 T L V ⊓ Subgroup.centralizer (V : Set G) = ch6ZS T L V ∧
      centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) ≤
        Subgroup.centralizer (uCh611 T L V : Set G) ∧
      ∀ t ∈ T ⊓ Subgroup.centralizer (V : Set G), ∃ v ∈ V,
        ∃ q ∈ pCoreOf 2 (hCh611 T), t = v * q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.normal_ch611_F4 h331 h432 h512 h614 h615
  have := h.commMod_ch611_F4 h331 h432 h512 h614 h615
  obtain ⟨h8, htop, hsq⟩ := h.stage_g31_ch611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  obtain ⟨hVC, -, hVUc, hCQ⟩ := h.step_a_ch611_F4 h331 h432 h512 h614 h615 h6210 h4
  set Z := zCh611 T with hZdef
  set H := hCh611 T with hHdef
  set U := uCh611 T L V with hUdef
  set ZS := ch6ZS T L V with hZSdef
  set ρ := rhoCh611 T L V with hρ
  set C := centralizerMod Z H U with hCdef
  have hV := h.toHyp611.isElemAbelian
  have hZZS : Z ≤ ZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  have hZ2 : Nat.card Z = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hZS4 : Nat.card ZS = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZSU : ZS ≤ U := le_conjClosure _ _
  have hUH : U ≤ H := h.uCh611_le_h_F4 h331 h432 h512 h614 h615
  have hVH : V ≤ H := h.V_le_hCh611
  have hTH : T ≤ H := T_le_hCh611 T
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := hCh611_le_normalizer_u T L V
  have hCH : C ≤ H := centralizerMod_le_left _ _ _
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_centralizerMod_ch62 (Subgroup.centralizer_le_normalizer _ hg)
      (Subgroup.le_normalizer hg) (le_normalizer_conjClosure _ H hg)
  obtain ⟨-, ⟨hCN, -, -⟩, -, -, -⟩ := h6210 G T M L V h
  have h9 := stmt6_2_9_F4 h331 h432 h512 h614 h615 G T M L V h

  let mk : ↥U → ↥U ⧸ Z.subgroupOf U := QuotientGroup.mk
  have hmk_eq : ∀ a b : ↥U, mk a = mk b ↔ (a : G)⁻¹ * b ∈ Z := fun a b => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hmk_one : ∀ a : ↥U, mk a = 1 ↔ (a : G) ∈ Z := fun a => by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set X₀ := quotSub U Z ZS with hX₀def

  obtain ⟨x₀, hx₀ZS, hx₀Z⟩ : ∃ x ∈ ZS, x ∉ Z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show ZS ≤ Z from hcon)
    omega
  set x₀' : ↥U := ⟨x₀, hZSU hx₀ZS⟩ with hx₀'
  have hx₀1 : mk x₀' ≠ 1 := fun h1 => hx₀Z ((hmk_one _).mp h1)
  have hX₀eq : X₀ = Subgroup.zpowers (mk x₀') := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact (mem_quotSub_iff hZZS x₀').mpr hx₀ZS
    · have h1 := card_quotSub (U := U) hZZS hZSU
      rw [← hX₀def, hZ2, hZS4] at h1
      rw [card_zpowers_of_sq (hsq _) hx₀1]
      omega
  have hmemX₀ : ∀ u : ↥U, mk u ∈ X₀ ↔ (u : G) ∈ ZS := fun u => mem_quotSub_iff hZZS u

  have hρv : ∀ v (hv : v ∈ V), IsTransvCh611 (mk x₀') (ρ ⟨v, hVH hv⟩) := by
    intro v hv x
    have hmem : ρ ⟨v, hVH hv⟩ x * x⁻¹ ∈ X₀ := by
      induction x using QuotientGroup.induction_on with
      | H u =>
        change ρ ⟨v, hVH hv⟩ (mk u) * (mk u)⁻¹ ∈ X₀
        rw [actQuot_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hmemX₀]
        have := hVUc (Subgroup.commutator_mem_commutator hv u.2)
        rw [commutatorElement_def] at this
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact this
    rw [hX₀eq] at hmem
    exact (mem_zpowers_iff_of_sq (hsq _)).mp hmem

  obtain ⟨v₀, hv₀V, hv₀C⟩ : ∃ v ∈ V, v ∉ C := by
    by_contra hcon
    push Not at hcon
    have : V ⊓ C = V := inf_eq_left.mpr hcon
    rw [hVC] at this
    have := congrArg (fun X : Subgroup G => Nat.card X) this
    rw [hZS4, h.natural.card_eq] at this
    norm_num at this
  have ht₀1 : ρ ⟨v₀, hVH hv₀V⟩ ≠ 1 := fun h1 =>
    hv₀C ((mem_centralizerMod_iff_actQuot' (hKU := hHU)
      (hKZ := hCh611_le_normalizer_z T) ⟨v₀, hVH hv₀V⟩).mpr h1)

  have hAV : ∀ τ : MulAut (↥U ⧸ Z.subgroupOf U), IsTransvCh611 (mk x₀') τ →
      ∃ v, ∃ hv : v ∈ V, ρ ⟨v, hVH hv⟩ = τ := by
    intro τ hτ
    by_cases hτ1 : τ = 1
    · exact ⟨1, V.one_mem, by rw [hτ1]; exact map_one ρ⟩
    obtain ⟨φ, hφx, hφ⟩ := exists_conj_transv_ch611 hsq hx₀1 (hρv v₀ hv₀V) hτ ht₀1 hτ1
    obtain ⟨k, hk⟩ : φ ∈ ρ.range := htop ▸ Subgroup.mem_top φ
    have hkX : quotSub U Z (conjSubgroup ZS (k : G)⁻¹) = quotSub U Z ZS := by
      rw [← map_actQuot_quotSub, ← hX₀def]
      change X₀.map (ρ k).toMonoidHom = X₀
      rw [hk, hX₀eq, map_zpowers_mulAut, hφx]
    have hZk : Z ≤ conjSubgroup ZS (k : G)⁻¹ := by
      intro z hz
      rw [mem_conjSubgroup_iff, inv_inv]
      have hkz := Subgroup.mem_centralizer_iff.mp k.2 z hz
      rw [mul_assoc, hkz, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hZZS hz
    have hkU : conjSubgroup ZS (k : G)⁻¹ ≤ U := by
      intro x hx
      rw [mem_conjSubgroup_iff, inv_inv] at hx
      have := (Subgroup.mem_normalizer_iff.mp (hHU k.2) _).mp (hZSU hx)
      simpa [mul_assoc] using this
    have h2 := eq_of_quotSub_eq hZk hZZS hkU hZSU hkX
    have hkN : (k : G) ∈ Subgroup.normalizer (ZS : Set G) := by
      have := Subgroup.inv_mem _ (conjSubgroup_eq_iff_mem_normalizer.mp h2)
      simpa using this
    have hkV : (k : G) ∈ Subgroup.normalizer (V : Set G) := by
      have : (k : G) ∈ H ⊓ Subgroup.normalizer (ZS : Set G) := ⟨k.2, hkN⟩
      rw [← h9.2.1] at this
      exact this.2
    have hkv : (k : G) * v₀ * (k : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hkV v₀).mp hv₀V
    refine ⟨_, hkv, ?_⟩
    have e : (⟨(k : G) * v₀ * (k : G)⁻¹, hVH hkv⟩ : ↥H) = k * ⟨v₀, hVH hv₀V⟩ * k⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, hk, ← hφ]

  have hUsq : ∀ u ∈ U, u ^ 2 = 1 := by
    intro u hu
    by_cases huZ : u ∈ Z
    · exact hV.2 u (hZZS huZ).1
    have hu1 : mk ⟨u, hu⟩ ≠ 1 := fun h1 => huZ ((hmk_one _).mp h1)
    obtain ⟨φ, hφ⟩ := exists_mulAut_apply_eq_ch611 hsq hx₀1 hu1
    obtain ⟨k, hk⟩ : φ ∈ ρ.range := htop ▸ Subgroup.mem_top φ
    have h1 : ρ k (mk x₀') = mk ⟨u, hu⟩ := by rw [hk, hφ]
    rw [show ρ k (mk x₀') = mk ⟨(k : G) * x₀ * (k : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hHU k.2) x₀).mp (hZSU hx₀ZS)⟩ from actQuot_mk k x₀',
      hmk_eq] at h1
    set a := (k : G) * x₀ * (k : G)⁻¹ with ha
    set z := a⁻¹ * u with hz
    have hzZ : z ∈ Z := h1
    have hua : u = a * z := by rw [hz]; group
    have ha2 : a ^ 2 = 1 := by
      rw [ha, conj_pow, hV.2 x₀ hx₀ZS.1, mul_one, mul_inv_cancel]
    have hz2 : z ^ 2 = 1 := hV.2 z (hZZS hzZ).1
    have haz : a * z = z * a := by
      have haH : a ∈ H := H.mul_mem (H.mul_mem k.2 (hVH hx₀ZS.1)) (H.inv_mem k.2)
      exact (Subgroup.mem_centralizer_iff.mp haH z hzZ).symm
    rw [hua, (Commute.mul_pow haz 2), ha2, hz2, one_mul]

  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have hinv : ∀ x ∈ U, x⁻¹ = x := fun x hx =>
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hUsq x hx)
    calc a * b = (a * b)⁻¹ := (hinv _ (U.mul_mem ha hb)).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv a ha, hinv b hb]

  have hU16 : Nat.card U = 16 := by
    have h1 := card_quotSub (U := U) (hZZS.trans hZSU) le_rfl
    have htopU : quotSub U Z U = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      induction x using QuotientGroup.induction_on with
      | H u => exact (mem_quotSub_iff (hZZS.trans hZSU) u).mpr u.2
    rw [htopU, Subgroup.card_top, h8, hZ2] at h1
    omega

  have hCUV : U ⊓ Subgroup.centralizer (V : Set G) = ZS := by
    apply le_antisymm
    · rintro u ⟨hu, huV⟩
      by_contra huZS
      have hu' : mk ⟨u, hu⟩ ∉ Subgroup.zpowers (mk x₀') := by
        rw [← hX₀eq, hmemX₀]
        exact huZS
      obtain ⟨τ, hτ, hτu⟩ := exists_transv_move_ch611 hsq hx₀1 hu'
      obtain ⟨v, hv, hvτ⟩ := hAV τ hτ
      apply hτu
      rw [← hvτ]
      change ρ ⟨v, hVH hv⟩ (mk ⟨u, hu⟩) = mk ⟨u, hu⟩
      rw [actQuot_mk]
      congr 1
      apply Subtype.ext
      show v * u * v⁻¹ = u
      rw [Subgroup.mem_centralizer_iff.mp huV v hv, mul_inv_cancel_right]
    · intro x hx
      exact ⟨hZSU hx, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        B2F.isElemAbelian_comm hV hv hx.1⟩
  refine ⟨hUsq, hUcomm, hU16, hCUV, ?_, ?_⟩
  ·

    have hφhom : ∀ c ∈ C, ∀ x ∈ U, ∀ y ∈ U,
        c * (x * y) * c⁻¹ * (x * y)⁻¹ = (c * x * c⁻¹ * x⁻¹) * (c * y * c⁻¹ * y⁻¹) := by
      intro c hc x hx y hy
      have hyZ := (mem_centralizerMod.mp hc).2.2 y hy
      have hcy : c * y * c⁻¹ * y⁻¹ * x⁻¹ = x⁻¹ * (c * y * c⁻¹ * y⁻¹) := by
        have hxH : x⁻¹ ∈ H := hUH (U.inv_mem hx)
        exact (Subgroup.mem_centralizer_iff.mp hxH _ hyZ)
      calc c * (x * y) * c⁻¹ * (x * y)⁻¹ = c * x * c⁻¹ * ((c * y * c⁻¹ * y⁻¹) * x⁻¹) := by
            group
        _ = c * x * c⁻¹ * (x⁻¹ * (c * y * c⁻¹ * y⁻¹)) := by rw [hcy]
        _ = _ := by group
    have hφconj : ∀ c ∈ C, ∀ v ∈ V, ∀ u ∈ U,
        c * (v * u * v⁻¹) * c⁻¹ * (v * u * v⁻¹)⁻¹ = c * u * c⁻¹ * u⁻¹ := by
      intro c hc v hv u hu
      set b := c⁻¹ * (v⁻¹ * c * v) with hb
      have hbV : b ∈ V := by
        have h1 : c⁻¹ * v⁻¹ * c ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hCN hc)) _).mp (V.inv_mem hv) |>
            fun h2 => by simpa [mul_assoc] using h2
        have : b = (c⁻¹ * v⁻¹ * c) * v := by rw [hb]; group
        rw [this]
        exact V.mul_mem h1 hv
      have hbC : b ∈ C := by
        have h1 : v⁻¹ * c * v ∈ C := by
          have := (Subgroup.mem_normalizer_iff.mp (hHC (hVH (V.inv_mem hv))) c).mp hc
          simpa using this
        exact C.mul_mem (C.inv_mem hc) h1
      have hbZS : b ∈ ZS := hVC ▸ (⟨hbV, hbC⟩ : b ∈ V ⊓ C)
      have hbu : b * u = u * b := hUcomm b (hZSU hbZS) u hu
      have hcu := (mem_centralizerMod.mp hc).2.2 u hu
      have hvZ : v * (c * u * c⁻¹ * u⁻¹) * v⁻¹ = c * u * c⁻¹ * u⁻¹ := by
        have := Subgroup.mem_centralizer_iff.mp (hVH hv) _ hcu
        rw [← this, mul_inv_cancel_right]
      have hvcv : v⁻¹ * c * v = c * b := by rw [hb]; group
      calc c * (v * u * v⁻¹) * c⁻¹ * (v * u * v⁻¹)⁻¹
          = v * ((v⁻¹ * c * v) * u * (v⁻¹ * c * v)⁻¹ * u⁻¹) * v⁻¹ := by group
        _ = v * (c * (b * u) * b⁻¹ * c⁻¹ * u⁻¹) * v⁻¹ := by rw [hvcv]; group
        _ = v * (c * u * c⁻¹ * u⁻¹) * v⁻¹ := by rw [hbu]; group
        _ = c * u * c⁻¹ * u⁻¹ := hvZ

    have hcomm1 : ∀ c ∈ C, ∀ v ∈ V, ∀ u ∈ U,
        c * (v * u * v⁻¹ * u⁻¹) = (v * u * v⁻¹ * u⁻¹) * c := by
      intro c hc v hv u hu
      have hvu : v * u * v⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hHU (hVH hv)) u).mp hu
      have h1 := hφhom c hc _ hvu _ (U.inv_mem hu)
      rw [hφconj c hc v hv u hu] at h1
      have h2 := hφhom c hc _ hu _ (U.inv_mem hu)
      rw [mul_inv_cancel, mul_one, inv_one, mul_one, mul_inv_cancel] at h2
      have h3 : c * (v * u * v⁻¹ * u⁻¹) * c⁻¹ * (v * u * v⁻¹ * u⁻¹)⁻¹ = 1 := by
        rw [h1, ← h2]
      calc c * (v * u * v⁻¹ * u⁻¹)
          = c * (v * u * v⁻¹ * u⁻¹) * c⁻¹ * (v * u * v⁻¹ * u⁻¹)⁻¹ *
              ((v * u * v⁻¹ * u⁻¹) * c) := by group
        _ = (v * u * v⁻¹ * u⁻¹) * c := by rw [h3, one_mul]

    obtain ⟨u₀, hu₀U, hu₀⟩ : ∃ u ∈ U, v₀ * u * v₀⁻¹ * u⁻¹ ∉ Z := by
      by_contra hcon
      push Not at hcon
      exact hv₀C (mem_centralizerMod.mpr ⟨hVH hv₀V, Subgroup.centralizer_le_normalizer _
        (hVH hv₀V), hcon⟩)
    set a := v₀ * u₀ * v₀⁻¹ * u₀⁻¹ with ha
    have haZS : a ∈ ZS := by
      have := hVUc (Subgroup.commutator_mem_commutator hv₀V hu₀U)
      rwa [commutatorElement_def] at this

    have hZSeq : Z ⊔ Subgroup.zpowers a = ZS := by
      apply Subgroup.eq_of_le_of_card_ge (sup_le hZZS ((Subgroup.zpowers_le).mpr haZS))
      have hlt : Z < Z ⊔ Subgroup.zpowers a := lt_of_le_of_ne le_sup_left fun h0 =>
        hu₀ (h0 ▸ (le_sup_right : Subgroup.zpowers a ≤ Z ⊔ Subgroup.zpowers a)
          (Subgroup.mem_zpowers a))
      have hdvd : Nat.card ↥(Z ⊔ Subgroup.zpowers a) ∣ 4 :=
        hZS4 ▸ Subgroup.card_dvd_of_le (sup_le hZZS ((Subgroup.zpowers_le).mpr haZS))
      have hgt : 2 < Nat.card ↥(Z ⊔ Subgroup.zpowers a) := by
        have h1 := Subgroup.card_lt_of_lt hlt
        omega
      rw [hZS4]
      have : Nat.card ↥(Z ⊔ Subgroup.zpowers a) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have h3 : Nat.card ↥(Z ⊔ Subgroup.zpowers a) ≠ 3 := fun h3 => by
        rw [h3] at hdvd
        norm_num at hdvd
      omega

    have hCZS : ∀ c ∈ C, ∀ w ∈ ZS, c * w = w * c := by
      intro c hc w hw
      have hle : Z ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({c} : Set G) := by
        refine sup_le (fun z hz => ?_) ((Subgroup.zpowers_le).mpr ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (hCH hc) z hz)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm1 c hc v₀ hv₀V u₀ hu₀U).symm
      rw [hZSeq] at hle
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm

    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hle : U ≤ Subgroup.centralizer ({c} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨k, hk, w, hw, rfl⟩
      have hck : k⁻¹ * c * k ∈ C := by
        have := (Subgroup.mem_normalizer_iff.mp (hHC (H.inv_mem hk)) c).mp hc
        simpa using this
      have h1 := hCZS _ hck w hw
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc k * w * k⁻¹ * c = k * (w * (k⁻¹ * c * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * c * k) * w) * k⁻¹ := by rw [h1]
        _ = c * (k * w * k⁻¹) := by group
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hu))
  ·
    rintro t ⟨htT, htV⟩
    have htcomm : ∀ τ : MulAut (↥U ⧸ Z.subgroupOf U), IsTransvCh611 (mk x₀') τ →
        ρ ⟨t, hTH htT⟩ * τ = τ * ρ ⟨t, hTH htT⟩ := by
      intro τ hτ
      obtain ⟨v, hv, rfl⟩ := hAV τ hτ
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp htV v hv).symm
    obtain ⟨v, hv, hvt⟩ := hAV _ (isTransv_of_comm_ch611 hsq hx₀1 htcomm)
    refine ⟨v, hv, v⁻¹ * t, ?_, by group⟩
    rw [← hCQ]
    have h1 : ρ ⟨v⁻¹ * t, H.mul_mem (H.inv_mem (hVH hv)) (hTH htT)⟩ = 1 := by
      have e : (⟨v⁻¹ * t, H.mul_mem (H.inv_mem (hVH hv)) (hTH htT)⟩ : ↥H) =
          (⟨v, hVH hv⟩ : ↥H)⁻¹ * ⟨t, hTH htT⟩ := Subtype.ext rfl
      rw [e, map_mul, map_inv, hvt, inv_mul_cancel]
    exact (mem_centralizerMod_iff_actQuot' (hKU := hHU) (hKZ := hCh611_le_normalizer_z T)
      _).mpr h1

end Hyp6Sec2

end CFSG.Quasithin.H13
