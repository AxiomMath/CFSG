module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14Ae5Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Ae5Gen

theorem commute_of_central_commutator {Y : Type} [Group Y] {z y : Y} (hz : z * z = 1) {N : ℕ}
    (hN : Odd N) (hy : y ^ N = 1)
    (hc : ∀ w : Y, w * (y * z * y⁻¹ * z⁻¹) = (y * z * y⁻¹ * z⁻¹) * w) : y * z = z * y := by
  set c := y * z * y⁻¹ * z⁻¹ with hcdef
  have hyz : y * z * y⁻¹ = c * z := by rw [hcdef]; group
  have hcc : c * c = 1 := by
    have h1 : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
      calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
        _ = 1 := by rw [hz]; group
    rw [hyz] at h1
    have h2 : (c * z) * (c * z) = c * c := by
      calc (c * z) * (c * z) = c * (z * c) * z := by group
        _ = c * (c * z) * z := by rw [hc z]
        _ = c * c * (z * z) := by group
        _ = c * c := by rw [hz, mul_one]
    rw [h2] at h1
    exact h1
  have hyc : y * c = c * y := hc y
  have hk : ∀ k : ℕ, y ^ k * z * (y ^ k)⁻¹ = c ^ k * z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcom : y * c ^ k = c ^ k * y := (Commute.pow_right (show Commute y c from hyc) k).eq
      calc y ^ (k + 1) * z * (y ^ (k + 1))⁻¹ = y * (y ^ k * z * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = y * (c ^ k * z) * y⁻¹ := by rw [ih]
        _ = (y * c ^ k * y⁻¹) * (y * z * y⁻¹) := by group
        _ = c ^ k * (c * z) := by
            rw [hyz, hcom]; group
        _ = c ^ (k + 1) * z := by rw [pow_succ]; group
  have hcN : c ^ N = 1 := by
    have := hk N
    rw [hy] at this
    simp only [inv_one, mul_one, one_mul] at this
    have h3 : c ^ N * z = 1 * z := by rw [one_mul]; exact this.symm
    exact mul_right_cancel h3
  obtain ⟨j, hj⟩ := hN
  have hc1 : c = 1 := by
    rw [hj, pow_succ, pow_mul, pow_two, hcc, one_pow, one_mul] at hcN
    exact hcN
  calc y * z = (y * z * y⁻¹ * z⁻¹) * (z * y) := by group
    _ = z * y := by rw [← hcdef, hc1, one_mul]


@[expose] noncomputable def psiOfF {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdent Δ 5) : Y →* AE.AEQ 5 where
  toFun y := I.φ ⟨y, F.gen ▸ Subgroup.mem_top y⟩
  map_one' := by
    rw [show (⟨1, F.gen ▸ Subgroup.mem_top 1⟩ : ↥(pSpan Δ)) = 1 from rfl, map_one]
  map_mul' := fun a b => by
    rw [show (⟨a * b, F.gen ▸ Subgroup.mem_top (a * b)⟩ : ↥(pSpan Δ)) =
      ⟨a, F.gen ▸ Subgroup.mem_top a⟩ * ⟨b, F.gen ▸ Subgroup.mem_top b⟩ from rfl, map_mul]

open Ae5Model in
theorem ae5Gen_of_prod (Y : Type) [Group Y] [Finite Y] (Δ : Set (Subgroup Y))
    (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdent Δ 5) (K : Subgroup Y) (hK : K ∈ Δ)
    (K' : Subgroup Y) (hK' : K' ∈ Δ) (hne : K' ≠ K) (z : Y) (hzK : IsUniqueInvolution K z)
    (hzK' : IsUniqueInvolution K' z) (hcomm : Commutes K K') (ι : Fin 4 ↪ Fin 5) (k : Y) (hk : k ∈ K)
    (k' : Y) (hk' : k' ∈ K')
    (hιK : ∀ (p : Fin 5) (b : Bool), K.map (psiOfF F I) = AE.memBar (miss p) (card_miss p) b →
      Set.range ι = ↑(miss p))
    (hprod : psiOfF F I (k * k') = AE.mkQ 5 (AE.embed ι w0)) :
    (k * k') * (k * k') = 1 ∧ k * k' ≠ 1 ∧
      Subgroup.centralizer ({z} : Set Y) ⊔ Subgroup.centralizer ({k * k'} : Set Y) = ⊤ := by
  have hΩ := F.hyp
  have hX : ∀ y : Y, y ∈ pSpan Δ := fun y => F.gen ▸ Subgroup.mem_top y
  let ψ : Y →* AE.AEQ 5 := psiOfF F I
  have hψ : ∀ y (hy : y ∈ pSpan Δ), ψ y = I.φ ⟨y, hy⟩ := fun y hy => rfl
  have map_psi : ∀ L : Subgroup Y, L.map ψ = (L.subgroupOf (pSpan Δ)).map I.φ := by
    intro L
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hX y⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    · rintro ⟨⟨y, hy'⟩, hy, rfl⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hrange : ∀ g : Y, ∃ x : AE.Wr 5, x ∈ AE.aeSub 5 ∧ AE.mkQ 5 x = ψ g := by
    intro g
    have : ψ g ∈ I.φ.range := ⟨_, rfl⟩
    rw [I.range_eq] at this
    exact this
  have hcent : ∀ g : Y, ψ g = 1 → ∀ w : Y, w * g = g * w := by
    intro g hg w
    have hg' : (⟨g, hX g⟩ : ↥(pSpan Δ)) ∈ I.φ.ker := hg
    have := Subgroup.mem_center_iff.mp (I.ker_le hg') ⟨w, hX w⟩
    exact congrArg Subtype.val this
  have hlab : ∀ L ∈ Δ, ∃ (p : Fin 5) (b : Bool),
      L.map ψ = AE.memBar (miss p) (card_miss p) b := by
    intro L hL
    obtain ⟨α, h, b, hl⟩ := I.label L hL
    obtain ⟨p, rfl⟩ := exists_miss h
    exact ⟨p, b, by rw [map_psi]; exact hl⟩
  have hinj : ∀ L ∈ Δ, ∀ M ∈ Δ, L.map ψ = M.map ψ → L = M := by
    intro L hL M hM hLM
    obtain ⟨a, haL, ha2⟩ := F.exists_mul_self_ne_one L hL
    refine TwinDisc.ExitO2.fam_eq_of_phi_mem I.φ F (le_refl 5) I.ker_le I.label hL hM haL ha2 ?_
    have := I.mem_map hL haL
    rw [← map_psi, hLM, map_psi] at this
    exact this
  have zimg : ∀ L ∈ Δ, ∀ (p : Fin 5) (b : Bool), L.map ψ = AE.memBar (miss p) (card_miss p) b →
      ∀ u : Y, IsUniqueInvolution L u → ψ u = AE.zBar (miss p) (card_miss p) := by
    intro L hL p b hl u hu
    have h8 : Nat.card ↥L = 8 := (F.card L hL).trans (by norm_num)
    exact I.map_eq_zBar (le_refl 5) hL h8 (by rw [← map_psi]; exact hl) hu
  obtain ⟨m, b, hKl⟩ := hlab K hK
  obtain ⟨m', b', hK'l⟩ := hlab K' hK'
  have hψz : ψ z = AE.zBar (miss m) (card_miss m) := zimg K hK m b hKl z hzK
  have hψz' : ψ z = AE.zBar (miss m') (card_miss m') := zimg K' hK' m' b' hK'l z hzK'
  obtain rfl : m = m' :=
    (miss_inj (AE.eq_of_zBar_eq (by norm_num) (hψz'.symm.trans hψz))).symm
  have hbb : b ≠ b' := by
    intro h
    subst h
    exact hne (hinj K' hK' K hK (by rw [hKl, hK'l]))
  have hbool : ∀ c : Bool, c = b ∨ c = b' := by
    intro c
    cases c <;> cases b <;> cases b' <;> simp_all
  have hι : Set.range ι = ↑(miss m) := hιK m b hKl
  have hιr : ∀ i : Fin 4, ι i ∈ miss m := by
    intro i
    have : ι i ∈ Set.range ι := Set.mem_range_self i
    rw [hι] at this
    exact_mod_cast this
  have hιm : ∀ i : Fin 4, ι i ≠ m := fun i h => by
    have := hιr i
    rw [h] at this
    simp [miss] at this
  have hιne : ∀ i j : Fin 4, i ≠ j → ι i ≠ ι j := fun i j hij h => hij (ι.injective h)
  set a := k * k' with ha
  set abar := AE.mkQ 5 (AE.embed ι w0) with habar
  have hψa : ψ a = abar := hprod
  have habar2 : abar * abar = 1 := by
    rw [habar, ← map_mul, embed_w0_mul_self, map_one]
  have habar1 : abar ≠ 1 := by
    intro h
    rw [habar, ← (AE.mkQ 5).map_one] at h
    exact embed_w0_ne_one ι (AE.mkQ_inj_of_supportedOn (le_refl 5) (AE.embed_supportedOn ι w0)
      (AE.supportedOn_one _) h)
  have hzne : ψ z ≠ 1 := by rw [hψz]; exact AE.zBar_ne_one (le_refl 5) _ _
  have hkk : k * k = 1 ∨ k * k = z := by
    apply hzK.unique (k * k) (K.mul_mem hk hk)
    have := F.pow_four K hK k hk
    calc k * k * (k * k) = k ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hkk' : k' * k' = 1 ∨ k' * k' = z := by
    apply hzK'.unique (k' * k') (K'.mul_mem hk' hk')
    have := F.pow_four K' hK' k' hk'
    calc k' * k' * (k' * k') = k' ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hcomm' : k * k' = k' * k := hcomm k hk k' hk'
  have haa : a * a = (k * k) * (k' * k') := by
    rw [ha]
    calc k * k' * (k * k') = k * (k' * k) * k' := by group
      _ = k * (k * k') * k' := by rw [hcomm']
      _ = (k * k) * (k' * k') := by group
  have ha2 : a * a = 1 := by
    have hψaa : ψ (a * a) = 1 := by rw [map_mul, hψa, habar2]
    rw [haa] at hψaa ⊢
    rcases hkk with h1 | h1 <;> rcases hkk' with h2 | h2
    · rw [h1, h2, one_mul]
    · rw [h1, h2, one_mul] at hψaa
      exact absurd hψaa hzne
    · rw [h1, h2, mul_one] at hψaa
      exact absurd hψaa hzne
    · rw [h1, h2, hzK.sq]
  have ha1 : a ≠ 1 := by
    intro h
    apply habar1
    rw [← hψa, h, map_one]
  have haKK : a ∈ K ⊔ K' := Subgroup.mul_mem_sup hk hk'
  refine ⟨ha2, ha1, ?_⟩
  have hmem_range : ∀ x : AE.Wr 5, x ∈ AE.aeSub 5 → AE.mkQ 5 x ∈ I.φ.range := by
    intro x hx
    rw [I.range_eq]
    exact Subgroup.mem_map_of_mem _ hx
  have hlift : ∀ x : AE.Wr 5, x ∈ AE.aeSub 5 → AE.mkQ 5 x ^ 3 = 1 →
      ∃ y : Y, ψ y = AE.mkQ 5 x ∧ ∃ N : ℕ, Odd N ∧ y ^ N = 1 := by
    intro x hx hx3
    obtain ⟨y, hyφ, N, hyN⟩ := I.exists_lift_pow_three (hmem_range x hx) hx3
    exact ⟨(y : Y), by rw [hψ _ y.2]; exact hyφ, 3 ^ N, Odd.pow (by decide),
      by rw [← Subgroup.coe_pow, hyN]; rfl⟩
  have hσ1d : ι 0 ≠ ι 1 := hιne 0 1 (by decide)
  have hσ1d' : ι 1 ≠ ι 2 := hιne 1 2 (by decide)
  have hσ1d'' : ι 0 ≠ ι 2 := hιne 0 2 (by decide)
  have hσ2d : ι 2 ≠ ι 3 := hιne 2 3 (by decide)
  have hσ2d' : ι 3 ≠ m := (hιm 3)
  have hσ2d'' : ι 2 ≠ m := (hιm 2)
  set σ1 := threeCycle (ι 0) (ι 1) (ι 2) with hσ1
  set σ2 := threeCycle (ι 2) (ι 3) m with hσ2
  have hm1 : σ1 m = m := threeCycle_of_ne (Ne.symm (hιm 0)) (Ne.symm (hιm 1)) (Ne.symm (hιm 2))
  obtain ⟨y1, hy1ψ, N1, hN1, hy1N⟩ : ∃ y : Y, ψ y = AE.mkQ 5 (AE.Wr.ofPerm σ1) ∧ ∃ N : ℕ, Odd N ∧ y ^ N = 1 := by
    have hyE := AE.yElt_of_perm (n := 5) (le_refl 5) (card_miss m) (σ := σ1)
      (fun x hx => by
        simp only [miss, Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
        intro h
        apply hx
        apply σ1.injective
        rw [h, hm1])
      (threeCycle_cubed hσ1d hσ1d' hσ1d'') ⟨ι 0, by simpa [miss] using hιr 0, by
        rw [hσ1, threeCycle_fst hσ1d hσ1d'']; exact hσ1d.symm⟩
    exact hlift _ (ofPerm_threeCycle_mem hσ1d hσ1d') hyE.1
  have hy1z : y1 * z = z * y1 := by
    refine commute_of_central_commutator hzK.sq hN1 hy1N (fun w => hcent _ ?_ w)
    have hyE := AE.yElt_of_perm (n := 5) (le_refl 5) (card_miss m) (σ := σ1)
      (fun x hx => by
        simp only [miss, Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
        intro h
        apply hx
        apply σ1.injective
        rw [h, hm1])
      (threeCycle_cubed hσ1d hσ1d' hσ1d'') ⟨ι 0, by simpa [miss] using hιr 0, by
        rw [hσ1, threeCycle_fst hσ1d hσ1d'']; exact hσ1d.symm⟩
    have hc := hyE.2.1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1ψ, hψz]
    calc _ = (AE.mkQ 5 (AE.Wr.ofPerm σ1) * AE.zBar (miss m) (card_miss m)) *
          (AE.mkQ 5 (AE.Wr.ofPerm σ1))⁻¹ * (AE.zBar (miss m) (card_miss m))⁻¹ := by group
      _ = 1 := by rw [hc]; group
  have hσ2a : σ2 (ι 0) = ι 0 :=
    threeCycle_of_ne hσ1d'' (hιne 0 3 (by decide)) (hιm 0)
  have hσ2b : σ2 (ι 1) = ι 1 :=
    threeCycle_of_ne (hιne 1 2 (by decide)) (hιne 1 3 (by decide)) (hιm 1)
  obtain ⟨y2, hy2ψ, N2, hN2, hy2N⟩ : ∃ y : Y, ψ y = AE.mkQ 5 (AE.Wr.ofPerm σ2) ∧ ∃ N : ℕ, Odd N ∧ y ^ N = 1 :=
    hlift _ (ofPerm_threeCycle_mem hσ2d hσ2d') (by
      rw [← map_pow, AE.ofPerm_pow, threeCycle_cubed hσ2d hσ2d' hσ2d'', AE.ofPerm_one, map_one])
  have hy2a : y2 * a = a * y2 := by
    refine commute_of_central_commutator ha2 hN2 hy2N (fun w => hcent _ ?_ w)
    have hc : AE.mkQ 5 (AE.Wr.ofPerm σ2) * abar = abar * AE.mkQ 5 (AE.Wr.ofPerm σ2) := by
      rw [habar, ← map_mul, ← map_mul, ofPerm_comm_embed_w0 ι hσ2a hσ2b]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy2ψ, hψa]
    calc _ = (AE.mkQ 5 (AE.Wr.ofPerm σ2) * abar) * (AE.mkQ 5 (AE.Wr.ofPerm σ2))⁻¹ * abar⁻¹ := by group
      _ = 1 := by rw [hc]; group
  set D : Subgroup Y := Subgroup.centralizer ({z} : Set Y) ⊔ Subgroup.centralizer ({a} : Set Y)
    with hD
  have hy1D : y1 ∈ D := Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hy1z)
  have hy2D : y2 ∈ D := Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr hy2a)
  have hKD : K ≤ D := fun w hw => Subgroup.mem_sup_left
    (Subgroup.mem_centralizer_singleton_iff.mpr (hzK.commute_of_mem hw).symm)
  have hK'D : K' ≤ D := fun w hw => Subgroup.mem_sup_left
    (Subgroup.mem_centralizer_singleton_iff.mpr (hzK'.commute_of_mem hw).symm)
  let Sp : Fin 5 → Prop := fun p => ∀ L ∈ Δ, ∀ c : Bool,
    L.map ψ = AE.memBar (miss p) (card_miss p) c → L ≤ D
  have hSm : Sp m := by
    intro L hL c hl
    rcases hbool c with rfl | rfl
    · have : L = K := hinj L hL K hK (by rw [hl, hKl])
      rw [this]; exact hKD
    · have : L = K' := hinj L hL K' hK' (by rw [hl, hK'l])
      rw [this]; exact hK'D
  have hclose : ∀ g ∈ D, ∀ x : AE.Wr 5, AE.mkQ 5 x = ψ g → ∀ p, Sp p → Sp (x.perm p) := by
    intro g hg x hx p hp L hL c hl
    obtain ⟨u, hu⟩ := (hΩ.omega1 L hL).1
    have hL' : conjSub g⁻¹ L ∈ Δ := hΩ.conjInvariant g⁻¹ L hL
    obtain ⟨q, c', hl'⟩ := hlab _ hL'
    have hu' := hu.conj g⁻¹
    have h1 : ψ u = AE.zBar (miss (x.perm p)) (card_miss _) := zimg L hL _ c hl u hu
    have h2 : ψ (g⁻¹ * u * g⁻¹⁻¹) = AE.zBar (miss p) (card_miss p) := by
      have e : ψ (g⁻¹ * u * g⁻¹⁻¹) = (ψ g)⁻¹ * ψ u * ψ g := by simp [map_mul, map_inv]
      rw [e, h1, ← hx]
      have := zBar_conj_miss x⁻¹ (x.perm p)
      rw [map_inv, AE.Wr.inv_perm, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
      simpa using this
    have h3 := zimg _ hL' q c' hl' _ hu'
    have hqp : q = p := (miss_inj (AE.eq_of_zBar_eq (by norm_num) (h3.symm.trans h2)))
    subst hqp
    have hL'D : conjSub g⁻¹ L ≤ D := hp _ hL' c' hl'
    intro l hlL
    have hx' : g⁻¹ * l * g ∈ conjSub g⁻¹ L := by
      rw [mem_conjSub_iff]
      simpa [mul_assoc] using hlL
    have := D.mul_mem (D.mul_mem hg (hL'D hx')) (D.inv_mem hg)
    simpa [mul_assoc] using this
  have hS1 : ∀ p, Sp p → Sp (σ1 p) := fun p hp =>
    hclose y1 hy1D (AE.Wr.ofPerm σ1) hy1ψ.symm p hp
  have hS2 : ∀ p, Sp p → Sp (σ2 p) := fun p hp =>
    hclose y2 hy2D (AE.Wr.ofPerm σ2) hy2ψ.symm p hp
  have hS2m : Sp (ι 2) := by
    have := hS2 m hSm
    rwa [hσ2, threeCycle_thd] at this
  have hS3 : Sp (ι 3) := by
    have := hS2 _ hS2m
    rwa [hσ2, threeCycle_fst hσ2d hσ2d''] at this
  have hS0 : Sp (ι 0) := by
    have := hS1 _ hS2m
    rwa [hσ1, threeCycle_thd] at this
  have hS1' : Sp (ι 1) := by
    have := hS1 _ hS0
    rwa [hσ1, threeCycle_fst hσ1d hσ1d''] at this
  have hall : ∀ p : Fin 5, Sp p := by
    intro p
    by_cases hp : p = m
    · rw [hp]; exact hSm
    · have hpm : p ∈ miss m := by simp [miss, hp]
      have : p ∈ Set.range ι := by
        rw [hι]; exact_mod_cast hpm
      obtain ⟨i, rfl⟩ := this
      fin_cases i
      · exact hS0
      · exact hS1'
      · exact hS2m
      · exact hS3
  have hle : pSpan Δ ≤ D := by
    refine pSpan_le (fun L hL => ?_)
    obtain ⟨p, c, hl⟩ := hlab L hL
    exact hall p L hL c hl
  rw [F.gen] at hle
  exact top_le_iff.mp hle

end Ae5Gen

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
