module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusBasic
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusInputs

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Omnibus

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

omit [Finite G] in
theorem mul_comm_of_subset_mul {V C W : Subgroup G} (hWV : W ≤ V)
    (hCW : C ≤ Subgroup.normalizer (W : Set G))
    (hV : (V : Set G) ⊆ ((V ⊓ C : Subgroup G) : Set G) * W) : (V : Set G) * C = C * V := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, hu, c, hc, rfl⟩
    obtain ⟨u₀, hu₀, w, hw, rfl⟩ := hV hu
    have hw' : c⁻¹ * w * c ∈ W := (Subgroup.mem_normalizer_iff''.mp (hCW hc) w).mp hw
    refine ⟨u₀ * c, C.mul_mem hu₀.2 hc, c⁻¹ * w * c, hWV hw', ?_⟩
    change u₀ * c * (c⁻¹ * w * c) = u₀ * w * c
    group
  · rintro _ ⟨c, hc, u, hu, rfl⟩
    obtain ⟨u₀, hu₀, w, hw, rfl⟩ := hV hu
    have hcu : c * u₀ ∈ C := C.mul_mem hc hu₀.2
    have hw' : c * u₀ * w * (c * u₀)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hCW hcu) w).mp hw
    refine ⟨c * u₀ * w * (c * u₀)⁻¹, hWV hw', c * u₀, hcu, ?_⟩
    change c * u₀ * w * (c * u₀)⁻¹ * (c * u₀) = c * (u₀ * w)
    group

section Sylow

theorem subset_inf_mul_of_comp (hσ : σ.IsValid) {V W : Subgroup G} (hV : Odd (Nat.card V))
    (hTV : σ.T ≤ Subgroup.normalizer (V : Set G)) (hW : ∀ i : Fin 3, comp σ V i ⊆ W) :
    (V : Set G) ⊆ ((V ⊓ σ.C : Subgroup G) : Set G) * W := by
  have := T_isKleinFour hσ
  obtain ⟨-, hdec⟩ := four_group_T_decomposition hV hTV σ.x_mem_T σ.x₂_mem_T (x_ne_one hσ)
    (x₂_ne_one hσ) hσ.x_ne_x₂
  obtain ⟨h0, h1, h2⟩ := fourInverted_subset_comp (σ := σ) V
  intro u hu
  rw [hdec] at hu
  obtain ⟨_, ⟨_, ⟨u₀, hu₀, v₁, hv₁, rfl⟩, v₂, hv₂, rfl⟩, v₃, hv₃, rfl⟩ := hu
  refine ⟨u₀, hu₀, v₁ * v₂ * v₃, ?_, by simp only [mul_assoc]⟩
  exact W.mul_mem (W.mul_mem (hW 0 (h0 hv₁)) (hW 1 (h1 hv₂))) (hW 2 (h2 hv₃))

omit [Finite G] in
theorem le_iSup_conjSub (W : Subgroup G) :
    W ≤ ⨆ c : σ.C, conjSub (c : G) W := by
  have := le_iSup (fun c : σ.C => conjSub (c : G) W) 1
  simpa using this

theorem mul_comm_of_isSylowOf (hσ : σ.IsValid) (Δ : Data σ r) (hN : ABG_II_4_11_Input Δ)
    {Y V : Subgroup G}
    (hY : Odd (Nat.card Y)) (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G))
    (hperm : (Y : Set G) * σ.C = σ.C * Y) (hV : IsSylowOf r V (Y ⊔ σ.C))
    (hTV : σ.T ≤ Subgroup.normalizer (V : Set G)) : (V : Set G) * σ.C = σ.C * V := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  set X : Subgroup G := Y ⊔ σ.C with hXdef
  have hX := hasNormalPComplement_sup hσ Δ hY hTY hperm
  set K : Subgroup G := oddCoreIn X with hKdef
  have hKodd : Odd (Nat.card K) := odd_card_oddCoreIn X
  have hCX : σ.C ≤ X := le_sup_right
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oddCoreIn X
  have hTK : σ.T ≤ Subgroup.normalizer (K : Set G) := ((σ.T_le_C hσ).trans hCX).trans hXK
  have hVp := hV.isPGroup
  have hVodd : Odd (Nat.card V) := odd_card_of_isPGroup Δ.prime Δ.ne_two hVp
  have hVK : V ≤ K := le_oddCoreIn_of_hasNormalPComplement hX hV.le hVodd
  have hVsylK : IsSylowOf r V K := hV.of_le hVK (oddCoreIn_le X)
  have hcomp : ∀ i : Fin 3, ∃ W : Subgroup G, W ≤ V ∧ (W : Set G) = comp σ V i ∧
      σ.C ≤ Subgroup.normalizer (W : Set G) := by
    intro i
    set Z : Subgroup G := K ⊓ σ.Ns i with hZdef
    have hZodd : Odd (Nat.card Z) := hKodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hCZ : σ.C ≤ Subgroup.normalizer (Z : Set G) := fun c hc =>
      mem_normalizer_inf (hXK (hCX hc)) (Subgroup.le_normalizer (C_le_Ns i hc))
    obtain ⟨P, hCP, hZP, Yi, hYi, hPY⟩ := hN i Z inf_le_right hZodd hCZ
    have hYb : IsBlock σ r i Yi := by
      rcases hYi with h | h | h
      · rw [h]; exact isBlock_Ps Δ i
      · rw [h]; exact isBlock_R Δ hσ i
      · rw [Set.mem_singleton_iff] at h
        rw [h]; exact isBlock_Rs Δ hσ i
    set W : Subgroup G := V ⊓ σ.Ns i ⊓ Yi with hWdef
    have hWcomp : (W : Set G) = comp σ V i := by
      ext v
      constructor
      · rintro ⟨⟨hvV, hvN⟩, hvY⟩
        exact ⟨hvV, mem_Ns_iff.mp hvN, hYb.inverted v hvY⟩
      · rintro ⟨hvV, hvx, hvinv⟩
        have hvN : v ∈ σ.Ns i := mem_Ns_iff.mpr hvx
        obtain ⟨c, hc, p, hp, hcp⟩ := hZP ⟨hVK hvV, hvN⟩
        have hcp' : c * p = v := hcp
        set x := σ.xs (i + 1) with hx
        have hxC : x ∈ σ.C := (σ.T_le_C hσ) (xs_mem_T (i + 1))
        have hxc : x * c * x⁻¹ = c := by
          rw [hx, comm_of_mem_C hc (xs_mem_T (i + 1))]
          group
        have hp' : x * p * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hCP hxC) p).mp hp
        set p' := x * p * x⁻¹ with hp'def
        have h1 : c * p' = p⁻¹ * c⁻¹ := by
          rw [← hcp', show x * (c * p) * x⁻¹ = (x * c * x⁻¹) * (x * p * x⁻¹) by group, hxc,
            mul_inv_rev] at hvinv
          exact hvinv
        have hcpc : c * p' * c⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hCP hc) _).mp hp'
        have hc2 : c * c ∈ P := by
          have : c * c = (c * p' * c⁻¹)⁻¹ * p⁻¹ := by
            calc c * c = (c * p' * c⁻¹)⁻¹ * (c * p' * c) := by group
              _ = (c * p' * c⁻¹)⁻¹ * p⁻¹ := by
                rw [show c * p' * c = p⁻¹ by rw [h1]; group]
          rw [this]
          exact P.mul_mem (P.inv_mem hcpc) (P.inv_mem hp)
        have hcpc' : c⁻¹ * p * c ∈ P := (Subgroup.mem_normalizer_iff''.mp (hCP hc) p).mp hp
        have hv2 : v ^ 2 ∈ P := by
          rw [← hcp', pow_two, show c * p * (c * p) = c * c * (c⁻¹ * p * c) * p by group]
          exact P.mul_mem (P.mul_mem hc2 hcpc') hp
        have hvP : v ∈ P := mem_of_sq_mem (odd_orderOf_of_mem hVodd hvV) hv2
        obtain ⟨k, hk⟩ := hVp ⟨v, hvV⟩
        have hvY : v ∈ Yi := hPY v hvP ⟨k, congrArg Subtype.val hk⟩
        exact ⟨⟨hvV, hvN⟩, hvY⟩
    set A : Subgroup G := ⨆ c : σ.C, conjSub (c : G) W with hAdef
    have hWA : W ≤ A := le_iSup_conjSub (σ := σ) W
    have hAY : A ≤ Yi := iSup_le fun c => by
      rw [conjSub_le_iff, conjSub_eq_self (Subgroup.inv_mem _ (hYb.normalized c.2))]
      exact inf_le_right
    have hAX : A ≤ X := iSup_le fun c => by
      rw [conjSub_le_iff, conjSub_eq_self_of_mem (X.inv_mem (hCX c.2))]
      exact inf_le_left.trans (inf_le_left.trans hV.le)
    have hCA : σ.C ≤ Subgroup.normalizer (A : Set G) := by
      intro c hc
      apply mem_normalizer_of_conj_le
      intro a ha
      have hle : conjSub c A ≤ A := by
        rw [hAdef, conjSub, Subgroup.map_iSup]
        exact iSup_le fun c' => le_iSup_of_le ⟨c * c', σ.C.mul_mem hc c'.2⟩
          (by rw [← conjSub, ← conjSub_mul])
      exact hle (conj_mem_conjSub ha)
    have hAp : IsPGroup r A := hYb.isPGroup.to_le hAY
    have hAodd : Odd (Nat.card A) := odd_card_of_isPGroup Δ.prime Δ.ne_two hAp
    have hAK : A ≤ K := le_oddCoreIn_of_hasNormalPComplement hX hAX hAodd
    have hTA : σ.T ≤ Subgroup.normalizer (A : Set G) := (σ.T_le_C hσ).trans hCA
    obtain ⟨Vs, hVs, hAVs, hTVs⟩ :=
      exists_isSylowOf_le_normalizer_of_le (T_isPGroup hσ) hKodd hTK hAK hAp hTA
    obtain ⟨c, ⟨-, hcT⟩, hcV⟩ :=
      exists_conj_of_isSylowOf_le_normalizer (T_isPGroup hσ) hKodd hTK hVsylK hVs hTV hTVs
    have hcC : c ∈ σ.C := hcT
    have hAW : A ≤ conjSub c W := by
      intro a ha
      have haV : a ∈ conjSub c V := by rw [hcV]; exact hAVs ha
      rw [mem_conjSub] at haV ⊢
      have haY : a ∈ Yi := hAY ha
      refine ⟨⟨haV, ?_⟩, (Subgroup.mem_normalizer_iff''.mp (hYb.normalized hcC) a).mp haY⟩
      exact (σ.Ns i).mul_mem ((σ.Ns i).mul_mem ((σ.Ns i).inv_mem (C_le_Ns i hcC))
        (hYb.le_Ns haY)) (C_le_Ns i hcC)
    have hWAeq : W = A := Subgroup.eq_of_le_of_card_ge hWA
      (by rw [← card_conjSub c W]; exact Subgroup.card_le_of_le hAW)
    refine ⟨W, inf_le_left.trans inf_le_left, hWcomp, ?_⟩
    rw [hWAeq]
    exact hCA
  choose W hWV hWcomp hCW using hcomp
  apply mul_comm_of_subset_mul (W := W 0 ⊔ W 1 ⊔ W 2)
  · exact sup_le (sup_le (hWV 0) (hWV 1)) (hWV 2)
  · intro c hc
    exact mem_normalizer_sup (mem_normalizer_sup (hCW 0 hc) (hCW 1 hc)) (hCW 2 hc)
  · apply subset_inf_mul_of_comp hσ hVodd hTV
    intro i
    rw [← hWcomp i]
    fin_cases i
    · exact fun v hv => Subgroup.mem_sup_left (Subgroup.mem_sup_left hv)
    · exact fun v hv => Subgroup.mem_sup_left (Subgroup.mem_sup_right hv)
    · exact fun v hv => Subgroup.mem_sup_right hv

theorem isSylowOf_sup_of_le (hσ : σ.IsValid) (Δ : Data σ r) (hN : ABG_II_4_11_Input Δ)
    {H U Y : Subgroup G} (hCH : σ.C ≤ H) (hYH : Y ≤ H) (hY : Odd (Nat.card Y))
    (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) (hperm : (Y : Set G) * σ.C = σ.C * Y)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) (hUY : U ≤ Y) :
    IsSylowOf r U (Y ⊔ σ.C) :=
  isSylowOf_sup_of_perm hσ Δ hCH hYH hY hTY hperm hU hUY fun _ hV _ hTV =>
    mul_comm_of_isSylowOf hσ Δ hN hY hTY hperm hV hTV

theorem oddCoreIn_sup_props (hσ : σ.IsValid) (Δ : Data σ r) {H U : Subgroup G}
    (hCH : σ.C ≤ H) (hU : U ∈ signalizersPerm H σ.T σ.C r) :
    Odd (Nat.card (oddCoreIn H ⊔ U : Subgroup G)) ∧
      σ.T ≤ Subgroup.normalizer ((oddCoreIn H ⊔ U : Subgroup G) : Set G) ∧
      ((oddCoreIn H ⊔ U : Subgroup G) : Set G) * σ.C = σ.C * (oddCoreIn H ⊔ U : Subgroup G) := by
  obtain ⟨⟨hUH, hUp, hTU, -⟩, hperm⟩ := hU
  set O : Subgroup G := oddCoreIn H with hOdef
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn H
  have hUO : U ≤ Subgroup.normalizer (O : Set G) := hUH.trans hHO
  have hCO : σ.C ≤ Subgroup.normalizer (O : Set G) := hCH.trans hHO
  have hcoe : ((O ⊔ U : Subgroup G) : Set G) = O * U :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hUO
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card O (O ⊔ U)
    rw [inf_eq_left.mpr le_sup_left, sup_comm,
      relIndex_sup_of_mul_comm (mul_comm_of_le_normalizer hUO), sup_comm] at h1
    rw [← h1]
    exact (((odd_card_of_isPGroup Δ.prime Δ.ne_two hUp).of_dvd_nat
      (Subgroup.relIndex_dvd_card _ _))).mul (odd_card_oddCoreIn H)
  · intro t ht
    exact mem_normalizer_sup (hHO (hCH ((σ.T_le_C hσ) ht))) (hTU ht)
  · rw [hcoe, mul_assoc, hperm, ← mul_assoc, ← mul_comm_of_le_normalizer hCO, mul_assoc]

theorem exists_isSylowOf_oddCoreIn_le (hσ : σ.IsValid) (Δ : Data σ r)
    (hN : ABG_II_4_11_Input Δ) {H U : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) :
    ∃ R₀ : Subgroup G, IsSylowOf r R₀ (oddCoreIn H) ∧ R₀ ≤ U := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨hYodd, hTY, hYperm⟩ := oddCoreIn_sup_props hσ Δ hCH hU.1
  have hUH : U ≤ H := hU.1.1.1
  have hYH : oddCoreIn H ⊔ U ≤ H := sup_le (oddCoreIn_le H) hUH
  have hsyl := isSylowOf_sup_of_le hσ Δ hN hCH hYH hYodd hTY hYperm hU le_sup_right
  refine ⟨U ⊓ oddCoreIn H, hsyl.inf_of_le_normalizer (le_sup_left.trans le_sup_left)
    ((sup_le hYH hCH).trans (le_normalizer_oddCoreIn H)), inf_le_left⟩

theorem exists_conj_of_le (hσ : σ.IsValid) (Δ : Data σ r) (hN : ABG_II_4_11_Input Δ)
    {H U U' Y : Subgroup G} (hCH : σ.C ≤ H) (hYH : Y ≤ H) (hY : Odd (Nat.card Y))
    (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) (hperm : (Y : Set G) * σ.C = σ.C * Y)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r))
    (hU' : U' ∈ maximals (signalizersPerm H σ.T σ.C r)) (hUY : U ≤ Y) (hU'Y : U' ≤ Y) :
    ∃ c ∈ σ.C ⊓ H, conjSub c U' = U := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  set X : Subgroup G := Y ⊔ σ.C with hXdef
  have hX := hasNormalPComplement_sup hσ Δ hY hTY hperm
  have hKodd : Odd (Nat.card (oddCoreIn X)) := odd_card_oddCoreIn X
  have hTK : σ.T ≤ Subgroup.normalizer ((oddCoreIn X : Subgroup G) : Set G) :=
    ((σ.T_le_C hσ).trans le_sup_right).trans (le_normalizer_oddCoreIn X)
  have hsyl := isSylowOf_sup_of_le hσ Δ hN hCH hYH hY hTY hperm hU hUY
  have hsyl' := isSylowOf_sup_of_le hσ Δ hN hCH hYH hY hTY hperm hU' hU'Y
  have hK : ∀ {V : Subgroup G}, IsSylowOf r V X → IsSylowOf r V (oddCoreIn X) := fun {V} hV =>
    hV.of_le (le_oddCoreIn_of_hasNormalPComplement hX hV.le
      (odd_card_of_isPGroup Δ.prime Δ.ne_two hV.isPGroup)) (oddCoreIn_le X)
  obtain ⟨c, ⟨hcK, hcT⟩, hc⟩ := exists_conj_of_isSylowOf_le_normalizer (T_isPGroup hσ) hKodd
    hTK (hK hsyl') (hK hsyl) hU'.1.1.2.2.1 hU.1.1.2.2.1
  exact ⟨c, ⟨hcT, (oddCoreIn_le X).trans (sup_le hYH hCH) hcK⟩, hc⟩

end Sylow

end CFSG.ABGTheoremB.TotallyInverted.Omnibus
