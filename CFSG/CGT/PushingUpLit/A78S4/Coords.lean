module

public import CFSG.CGT.PushingUpLit.A78S4.H1

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

namespace S4Side.Frame

variable {G : Type} [Group G] [Finite G] {L V W Z T : Subgroup G} {e : ℕ}
  {h : S4Side G L V W Z T e} {D : NatCoordK G L V Z (GaloisField 2 e)} (fr : Frame h D)

theorem b_one : fr.b 1 = 0 := fr.b_of_mem_V (Subgroup.one_mem _)

theorem a_one : fr.a 1 = 0 := (fr.mem_W_iff_a (Subgroup.one_mem _)).1 (Subgroup.one_mem _)

theorem b_inv {j : G} (hj : j ∈ V ⊔ W) : fr.b j⁻¹ = fr.b j := by
  have h1 := fr.b_mul hj (inv_mem hj)
  rw [mul_inv_cancel, fr.b_one] at h1
  have := eq_neg_of_add_eq_zero_right h1.symm
  rw [this, CharTwo.neg_eq]

theorem a_inv {j : G} (hj : j ∈ V ⊔ W) : fr.a j⁻¹ = fr.a j := by
  have h1 := fr.a_mul hj (inv_mem hj)
  rw [mul_inv_cancel, fr.a_one] at h1
  have := eq_neg_of_add_eq_zero_right h1.symm
  rw [this, CharTwo.neg_eq]

theorem a_of_mem_W {w : G} (hw : w ∈ W) : fr.a w = 0 :=
  (fr.mem_W_iff_a (Subgroup.mem_sup_right hw)).1 hw

end S4Side.Frame

namespace S4Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ}
  (P : S4Pair G L₁ L₂ V W Z Z₂ T e) (hZ : Z ≠ ⊥)

include P hZ

theorem c₂_conj_eq {D₂ : NatCoordK G L₂ W Z₂ (GaloisField 2 e)} (fr₂ : S4Side.Frame P.side₂ D₂)
    {x : G} (hxL : x ∈ L₁) (hxW : x ∈ Subgroup.normalizer (W : Set G)) {n : G}
    (hn : n ∈ V ⊓ W) : fr₂.c (x * n * x⁻¹) = fr₂.c n := by
  obtain ⟨z, hz, z₂, hz₂, rfl⟩ := P.exists_decomp hZ hn
  have hxz : x * z * x⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.1 (P.side₁.Z_cent hz) x hxL]
    group
  have hxz₂ := P.conj_Z₂ hxW hz₂
  have e1 : x * (z * z₂) * x⁻¹ = (x * z * x⁻¹) * (x * z₂ * x⁻¹) := by group
  have hzW : z ∈ W := (P.side₁.Z_le_N hz).2
  rw [e1, hxz, fr₂.c_mul hzW (P.side₂.Z_le_V hxz₂), fr₂.c_mul hzW (P.side₂.Z_le_V hz₂),
    fr₂.c_of_mem_Z hxz₂, fr₂.c_of_mem_Z hz₂]

theorem sp4Coords : Sp4Coords G (V ⊔ W) V W Z Z₂ (GaloisField 2 e) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D₁⟩ := P.side₁.nat
  obtain ⟨fr₁⟩ := P.side₁.exists_frame D₁
  obtain ⟨D₂⟩ := P.side₂.nat
  obtain ⟨fr₂⟩ := P.side₂.exists_frame D₂
  have hJJ : ∀ {x : G}, x ∈ V ⊔ W → x ∈ W ⊔ V := fun hx => by rwa [sup_comm]
  have hNN : ∀ {x : G}, x ∈ V ⊓ W → x ∈ W ⊓ V := fun hx => by rwa [inf_comm]
  obtain ⟨B, hBW, hBV, hVB⟩ := P.side₁.jst.exists_complement
  obtain ⟨A, hAV, hAW, hWA⟩ := P.side₂.jst.exists_complement
  have hβ : ∀ s : GaloisField 2 e, ∃ β ∈ B, fr₁.b β = s := by
    intro s
    obtain ⟨x, hx, -, hxs⟩ := fr₁.surj_ab 0 s
    rw [← hVB] at hx
    obtain ⟨v, hv, β, hβB, rfl⟩ := (mem_sup_iff_of_normalizes fun b hb v hv =>
      P.side₁.jst.conj_V b (Subgroup.mem_sup_right (hBW hb)) v hv).1 hx
    refine ⟨β, hβB, ?_⟩
    rw [← hxs, fr₁.b_mul (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right (hBW hβB)),
      fr₁.b_of_mem_V hv, zero_add]
  have hα : ∀ r : GaloisField 2 e, ∃ α ∈ A, fr₁.a α = r := by
    intro r
    obtain ⟨x, hx, hxr, -⟩ := fr₁.surj_ab r 0
    have hx' : x ∈ W ⊔ A := by rw [hWA]; exact hJJ hx
    obtain ⟨w, hw, α, hαA, rfl⟩ := (mem_sup_iff_of_normalizes fun a ha w hw =>
      P.side₁.jst.conj_V₂ a (Subgroup.mem_sup_left (hAV ha)) w hw).1 hx'
    refine ⟨α, hαA, ?_⟩
    rw [← hxr, fr₁.a_mul (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left (hAV hαA)),
      fr₁.a_of_mem_W hw, zero_add]
  choose βf hβB hβb using hβ
  choose αf hαA hαa using hα
  have hβJ : ∀ s, βf s ∈ V ⊔ W := fun s => Subgroup.mem_sup_right (hBW (hβB s))
  have hαJ : ∀ r, αf r ∈ V ⊔ W := fun r => Subgroup.mem_sup_left (hAV (hαA r))
  have hβu : ∀ β ∈ B, βf (fr₁.b β) = β := by
    intro β hβ'
    have hβJ' : β ∈ V ⊔ W := Subgroup.mem_sup_right (hBW hβ')
    have h1 : βf (fr₁.b β) * β⁻¹ ∈ B ⊓ V := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (hβB _) (inv_mem hβ'), ?_⟩
      rw [fr₁.mem_V_iff_b (mul_mem (hβJ _) (inv_mem hβJ')), fr₁.b_mul (hβJ _) (inv_mem hβJ'),
        fr₁.b_inv hβJ', hβb, CharTwo.add_self_eq_zero]
    rw [hBV, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.1 h1
  have hαu : ∀ α ∈ A, αf (fr₁.a α) = α := by
    intro α hα'
    have hαJ' : α ∈ V ⊔ W := Subgroup.mem_sup_left (hAV hα')
    have h1 : αf (fr₁.a α) * α⁻¹ ∈ A ⊓ W := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (hαA _) (inv_mem hα'), ?_⟩
      rw [fr₁.mem_W_iff_a (mul_mem (hαJ _) (inv_mem hαJ')), fr₁.a_mul (hαJ _) (inv_mem hαJ'),
        fr₁.a_inv hαJ', hαa, CharTwo.add_self_eq_zero]
    rw [hAW, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.1 h1
  have hβadd : ∀ s s', βf (s + s') = βf s * βf s' := by
    intro s s'
    have h1 := hβu _ (mul_mem (hβB s) (hβB s'))
    rw [fr₁.b_mul (hβJ s) (hβJ s'), hβb, hβb] at h1
    exact h1
  have hαadd : ∀ r r', αf (r + r') = αf r * αf r' := by
    intro r r'
    have h1 := hαu _ (mul_mem (hαA r) (hαA r'))
    rw [fr₁.a_mul (hαJ r) (hαJ r'), hαa, hαa] at h1
    exact h1
  have hβ0 : βf 0 = 1 := by
    have h1 := hβu 1 B.one_mem
    rwa [fr₁.b_one] at h1
  have hα0 : αf 0 = 1 := by
    have h1 := hαu 1 A.one_mem
    rwa [fr₁.a_one] at h1
  set nn : G → G := fun x => (βf (fr₁.b x) * αf (fr₁.a x))⁻¹ * x with hnn_def
  have hnn : ∀ x ∈ V ⊔ W, nn x ∈ V ⊓ W := by
    intro x hx
    have hm : (βf (fr₁.b x) * αf (fr₁.a x))⁻¹ ∈ V ⊔ W := inv_mem (mul_mem (hβJ _) (hαJ _))
    have hnJ : nn x ∈ V ⊔ W := mul_mem hm hx
    have e1 : nn x = (αf (fr₁.a x))⁻¹ * (βf (fr₁.b x))⁻¹ * x := by
      simp only [hnn_def]; group
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [fr₁.mem_V_iff_b hnJ, e1, fr₁.b_mul (mul_mem (inv_mem (hαJ _)) (inv_mem (hβJ _))) hx,
        fr₁.b_mul (inv_mem (hαJ _)) (inv_mem (hβJ _)), fr₁.b_inv (hαJ _), fr₁.b_inv (hβJ _),
        fr₁.b_of_mem_V (hAV (hαA _)), hβb, zero_add, CharTwo.add_self_eq_zero]
    · rw [fr₁.mem_W_iff_a hnJ, e1, fr₁.a_mul (mul_mem (inv_mem (hαJ _)) (inv_mem (hβJ _))) hx,
        fr₁.a_mul (inv_mem (hαJ _)) (inv_mem (hβJ _)), fr₁.a_inv (hαJ _), fr₁.a_inv (hβJ _),
        fr₁.a_of_mem_W (hBW (hβB _)), hαa, add_zero, CharTwo.add_self_eq_zero]
  have hdec : ∀ x : G, x = βf (fr₁.b x) * αf (fr₁.a x) * nn x := fun x => by
    simp only [hnn_def]; group
  have hnn_mul : ∀ x ∈ V ⊔ W, ∀ y ∈ V ⊔ W,
      nn (x * y) = ⁅αf (fr₁.a x), βf (fr₁.b y)⁆ * nn x * nn y := by
    intro x hx y hy
    have hb : βf (fr₁.b (x * y)) = βf (fr₁.b x) * βf (fr₁.b y) := by
      rw [fr₁.b_mul hx hy, hβadd]
    have ha : αf (fr₁.a (x * y)) = αf (fr₁.a x) * αf (fr₁.a y) := by
      rw [fr₁.a_mul hx hy, hαadd]
    set βx := βf (fr₁.b x) with hβx
    set αx := αf (fr₁.a x) with hαx
    set βy := βf (fr₁.b y) with hβy
    set αy := αf (fr₁.a y) with hαy
    set n := nn x with hn
    set n' := nn y with hn'
    set c := ⁅αx, βy⁆ with hc
    have hnN := hnn x hx
    have hcN : c ∈ V ⊓ W := P.side₁.jst.commutator_mem (hAV (hαA _)) (hBW (hβB _))
    have h1 : n * (βy * αy) = (βy * αy) * n :=
      (P.side₁.jst.commute_of_mem_inf hnN (mul_mem (hβJ _) (hαJ _))).eq
    have h2 : αx * βy = c * βy * αx := by rw [hc, commutatorElement_def]; group
    have h3 : c * (βy * αx * αy) = (βy * αx * αy) * c :=
      (P.side₁.jst.commute_of_mem_inf hcN (mul_mem (mul_mem (hβJ _) (hαJ _)) (hαJ _))).eq
    have hxy : x * y = (βx * αx * n) * (βy * αy * n') := by
      rw [← hdec x, ← hdec y]
    show (βf (fr₁.b (x * y)) * αf (fr₁.a (x * y)))⁻¹ * (x * y) = c * n * n'
    rw [hb, ha, hxy]
    calc (βx * βy * (αx * αy))⁻¹ * (βx * αx * n * (βy * αy * n')) =
          (βx * βy * (αx * αy))⁻¹ * (βx * αx * (n * (βy * αy)) * n') := by group
      _ = (βx * βy * (αx * αy))⁻¹ * (βx * (αx * βy) * αy * n * n') := by rw [h1]; group
      _ = (βx * βy * (αx * αy))⁻¹ * (βx * (c * (βy * αx * αy)) * n * n') := by rw [h2]; group
      _ = (βx * βy * (αx * αy))⁻¹ * (βx * ((βy * αx * αy) * c) * n * n') := by rw [h3]
      _ = c * n * n' := by group
  set φ : GaloisField 2 e → GaloisField 2 e := fun r => fr₂.b (αf r) with hφ
  set ψ : GaloisField 2 e → GaloisField 2 e := fun s => fr₂.a (βf s) with hψ
  have hb₂ : ∀ x ∈ V ⊔ W, fr₂.b x = φ (fr₁.a x) := by
    intro x hx
    have hd : x * (αf (fr₁.a x))⁻¹ ∈ W := by
      rw [fr₁.mem_W_iff_a (mul_mem hx (inv_mem (hαJ _))), fr₁.a_mul hx (inv_mem (hαJ _)),
        fr₁.a_inv (hαJ _), hαa, CharTwo.add_self_eq_zero]
    have h1 := fr₂.b_mul (hJJ (mul_mem hx (inv_mem (hαJ (fr₁.a x))))) (hJJ (hαJ (fr₁.a x)))
    rw [inv_mul_cancel_right, fr₂.b_of_mem_V hd, zero_add] at h1
    exact h1
  have ha₂ : ∀ x ∈ V ⊔ W, fr₂.a x = ψ (fr₁.b x) := by
    intro x hx
    have hd : x * (βf (fr₁.b x))⁻¹ ∈ V := by
      rw [fr₁.mem_V_iff_b (mul_mem hx (inv_mem (hβJ _))), fr₁.b_mul hx (inv_mem (hβJ _)),
        fr₁.b_inv (hβJ _), hβb, CharTwo.add_self_eq_zero]
    have h1 := fr₂.a_mul (hJJ (mul_mem hx (inv_mem (hβJ (fr₁.b x))))) (hJJ (hβJ (fr₁.b x)))
    rw [inv_mul_cancel_right, fr₂.a_of_mem_W hd, zero_add] at h1
    exact h1
  have hc₂comm : ∀ α ∈ V, ∀ β ∈ W, fr₂.c ⁅α, β⁆ = φ (fr₁.a α) * ψ (fr₁.b β) := by
    intro α hαV β hβW
    have e1 : ⁅α, β⁆ = ⁅β, α⁆⁻¹ := by simp only [commutatorElement_def]; group
    have hcW : ⁅β, α⁆ ∈ W := (P.side₂.jst.commutator_mem hβW hαV).1
    rw [e1, fr₂.c_inv hcW, fr₂.c_comm hβW hαV, ← fr₂.a_vw hβW (Subgroup.one_mem V), mul_one,
      ha₂ β (Subgroup.mem_sup_right hβW), hb₂ α (Subgroup.mem_sup_left hαV), mul_comm]
  have hφadd : ∀ r r', φ (r + r') = φ r + φ r' := by
    intro r r'
    simp only [hφ]
    rw [hαadd, fr₂.b_mul (hJJ (hαJ r)) (hJJ (hαJ r'))]
  have hψadd : ∀ s s', ψ (s + s') = ψ s + ψ s' := by
    intro s s'
    simp only [hψ]
    rw [hβadd, fr₂.a_mul (hJJ (hβJ s)) (hJJ (hβJ s'))]
  have hφ0 : ∀ r, φ r = 0 → r = 0 := by
    intro r h0
    have h1 : αf r ∈ W := (fr₂.mem_V_iff_b (hJJ (hαJ r))).2 h0
    have h2 : αf r ∈ A ⊓ W := Subgroup.mem_inf.2 ⟨hαA r, h1⟩
    rw [hAW, Subgroup.mem_bot] at h2
    rw [← hαa r, h2, fr₁.a_one]
  have hψ0 : ∀ s, ψ s = 0 → s = 0 := by
    intro s h0
    have h1 : βf s ∈ V := (fr₂.mem_W_iff_a (hJJ (hβJ s))).2 h0
    have h2 : βf s ∈ B ⊓ V := Subgroup.mem_inf.2 ⟨hβB s, h1⟩
    rw [hBV, Subgroup.mem_bot] at h2
    rw [← hβb s, h2, fr₁.b_one]
  let ℬ : GaloisField 2 e →+ GaloisField 2 e →+ GaloisField 2 e :=
    AddMonoidHom.mk' (fun r => AddMonoidHom.mk' (fun s => φ r * ψ s) fun s s' => by
      rw [hψadd, mul_add]) fun r r' => AddMonoidHom.ext fun s => by
        show φ (r + r') * ψ s = φ r * ψ s + φ r' * ψ s
        rw [hφadd, add_mul]
  have hℬ : ∀ r s, ℬ r s = φ r * ψ s := fun _ _ => rfl
  have hinv : ∀ (l : (GaloisField 2 e)ˣ) (r s : GaloisField 2 e),
      ℬ ((l⁻¹ : (GaloisField 2 e)ˣ) * r) ((l : GaloisField 2 e) ^ 2 * s) = ℬ r s := by
    intro l r s
    obtain ⟨x, hxL, hxJ, hxW, hxab, -⟩ := fr₁.torus (Units.ne_zero l)
    have hxW' : x ∈ Subgroup.normalizer (W : Set G) := mem_normalizer_of_conj_le hxW
    have hαV : αf r ∈ V := hAV (hαA r)
    have hβW : βf s ∈ W := hBW (hβB s)
    have hxα : x * αf r * x⁻¹ ∈ V := D₁.norm x hxL _ hαV
    have hxβ : x * βf s * x⁻¹ ∈ W := hxW _ hβW
    have ha' := (hxab _ (hαJ r)).1
    have hb' := (hxab _ (hβJ s)).2
    rw [hαa] at ha'
    rw [hβb] at hb'
    have e1 : ⁅x * αf r * x⁻¹, x * βf s * x⁻¹⁆ = x * ⁅αf r, βf s⁆ * x⁻¹ := by
      simp only [commutatorElement_def]; group
    have h1 := hc₂comm _ hxα _ hxβ
    rw [e1, P.c₂_conj_eq hZ fr₂ hxL hxW' (P.side₁.jst.commutator_mem hαV hβW),
      hc₂comm _ hαV _ hβW, hαa, hβb, ha', hb'] at h1
    rw [hℬ, hℬ, Units.val_inv_eq_inv_val]
    exact h1.symm
  obtain ⟨κ, hκ⟩ := exists_kappa_of_invariant ℬ hinv
  have hfrob : Function.Surjective (fun r : GaloisField 2 e => r ^ 2) := by
    have hinj : Function.Injective (frobenius (GaloisField 2 e) 2) :=
      frobenius_inj (GaloisField 2 e) 2
    have hs := Finite.surjective_of_injective hinj
    intro y
    obtain ⟨r, hr⟩ := hs y
    exact ⟨r, by rw [← hr, frobenius_def]⟩
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨r, rfl⟩ := hfrob y
    have h1 := hκ r 1
    rw [mul_one, hy, hℬ] at h1
    have hψ1 : ψ 1 ≠ 0 := fun h0 => one_ne_zero (hψ0 1 h0)
    have hr : φ r = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hψ1
    show r ^ 2 = 0
    rw [hφ0 r hr]
    ring
  have hκbij : Function.Bijective κ := ⟨hκinj, Finite.surjective_of_injective hκinj⟩
  set κe := Equiv.ofBijective κ hκbij with hκe
  have hκe_add : ∀ a b, κe.symm (a + b) = κe.symm a + κe.symm b := by
    intro a b
    apply κe.injective
    rw [Equiv.apply_symm_apply]
    show a + b = κ (κe.symm a + κe.symm b)
    rw [map_add]
    show a + b = κe (κe.symm a) + κe (κe.symm b)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hκe_zero : κe.symm 0 = 0 := by
    apply κe.injective
    rw [Equiv.apply_symm_apply]
    show 0 = κ 0
    rw [map_zero]
  have hκe_κ : ∀ y, κe.symm (κ y) = y := fun y => κe.symm_apply_apply y
  refine ⟨⟨fun x => fr₁.a x, fun x => fr₁.b x, fun x => fr₁.c (nn x),
    fun x => κe.symm (fr₂.c (nn x)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro x hx y hy
    have hnx := hnn x hx
    have hny := hnn y hy
    have hcN : ⁅αf (fr₁.a x), βf (fr₁.b y)⁆ ∈ V ⊓ W :=
      P.side₁.jst.commutator_mem (hAV (hαA _)) (hBW (hβB _))
    refine ⟨fr₁.a_mul hx hy, fr₁.b_mul hx hy, ?_, ?_⟩
    · show fr₁.c (nn (x * y)) = fr₁.c (nn x) + fr₁.c (nn y) + fr₁.a x * fr₁.b y
      rw [hnn_mul x hx y hy, fr₁.c_mul (mul_mem hcN.1 hnx.1) hny.1, fr₁.c_mul hcN.1 hnx.1,
        fr₁.c_comm (hAV (hαA _)) (hBW (hβB _)), ← fr₁.a_vw (hAV (hαA _)) (Subgroup.one_mem W),
        mul_one, hαa, hβb]
      ring
    · show κe.symm (fr₂.c (nn (x * y))) = κe.symm (fr₂.c (nn x)) + κe.symm (fr₂.c (nn y)) +
        fr₁.a x ^ 2 * fr₁.b y
      rw [hnn_mul x hx y hy, fr₂.c_mul (mul_mem hcN.2 hnx.2) hny.2, fr₂.c_mul hcN.2 hnx.2,
        hc₂comm _ (hAV (hαA _)) _ (hBW (hβB _)), hαa, hβb, ← hℬ, hκ, hκe_add, hκe_add, hκe_κ]
      ring
  ·
    intro x hx y hy hr hs ht hw
    have hnx := hnn x hx
    have hny := hnn y hy
    have h1 := fr₁.c_inj_of_inf hnx hny ht
    have h2 : fr₂.c (nn x) = fr₂.c (nn y) := κe.symm.injective hw
    have h3 := fr₂.c_inj_of_inf (hNN hnx) (hNN hny) h2
    have h4 : nn x * (nn y)⁻¹ ∈ Z ⊓ Z₂ := Subgroup.mem_inf.2 ⟨h1, h3⟩
    rw [P.inf_Z, Subgroup.mem_bot] at h4
    have h5 := mul_inv_eq_one.1 h4
    rw [hdec x, hdec y]
    simp only at hr hs
    rw [hr, hs, h5]
  ·
    intro a b c d
    obtain ⟨z, hz, hzd⟩ := P.zc_surj fr₂ hZ (κ d)
    obtain ⟨z₂, hz₂, hz₂c⟩ := P.symm.zc_surj fr₁ (P.Z₂_ne_bot hZ) c
    have hzN := P.side₁.Z_le_N hz
    have hz₂N := P.Z₂_le_N hz₂
    have hnJ : z * z₂ ∈ V ⊔ W := Subgroup.mem_sup_left (mul_mem hzN.1 hz₂N.1)
    set x := βf b * αf a * (z * z₂) with hx
    have hxJ : x ∈ V ⊔ W := mul_mem (mul_mem (hβJ b) (hαJ a)) hnJ
    have hxa : fr₁.a x = a := by
      rw [hx, fr₁.a_mul (mul_mem (hβJ b) (hαJ a)) hnJ, fr₁.a_mul (hβJ b) (hαJ a),
        fr₁.a_of_mem_W (hBW (hβB b)), hαa, fr₁.a_of_mem_W (mul_mem hzN.2 hz₂N.2), zero_add,
        add_zero]
    have hxb : fr₁.b x = b := by
      rw [hx, fr₁.b_mul (mul_mem (hβJ b) (hαJ a)) hnJ, fr₁.b_mul (hβJ b) (hαJ a), hβb,
        fr₁.b_of_mem_V (hAV (hαA a)), fr₁.b_of_mem_V (mul_mem hzN.1 hz₂N.1), add_zero, add_zero]
    have hnx : nn x = z * z₂ := by
      simp only [hnn_def]
      rw [hxa, hxb, hx]
      group
    refine ⟨x, hxJ, hxa, hxb, ?_, ?_⟩
    · show fr₁.c (nn x) = c
      rw [hnx, fr₁.c_mul hzN.1 hz₂N.1, fr₁.c_of_mem_Z hz, hz₂c, zero_add]
    · show κe.symm (fr₂.c (nn x)) = d
      rw [hnx, fr₂.c_mul hzN.2 hz₂N.2, fr₂.c_of_mem_Z hz₂, hzd, add_zero, hκe_κ]
  ·
    intro x hx
    exact fr₁.mem_V_iff_b hx
  ·
    intro x hx
    exact fr₁.mem_W_iff_a hx
  ·
    intro x hx
    constructor
    · intro hxZ
      have hxN := P.side₁.Z_le_N hxZ
      have ha0 : fr₁.a x = 0 := fr₁.a_of_mem_W hxN.2
      have hb0 : fr₁.b x = 0 := fr₁.b_of_mem_V hxN.1
      have hnx : nn x = x := by
        simp only [hnn_def]
        rw [ha0, hb0, hα0, hβ0]
        group
      refine ⟨ha0, hb0, ?_⟩
      show fr₁.c (nn x) = 0
      rw [hnx, fr₁.c_of_mem_Z hxZ]
    · rintro ⟨ha0, hb0, ht0⟩
      replace ha0 : fr₁.a x = 0 := ha0
      replace hb0 : fr₁.b x = 0 := hb0
      have hxN : x ∈ V ⊓ W :=
        Subgroup.mem_inf.2 ⟨(fr₁.mem_V_iff_b hx).2 hb0, (fr₁.mem_W_iff_a hx).2 ha0⟩
      have hnx : nn x = x := by
        simp only [hnn_def]
        rw [ha0, hb0, hα0, hβ0]
        group
      have ht0' : fr₁.c (nn x) = 0 := ht0
      rw [hnx] at ht0'
      exact (fr₁.c_eq_zero_iff hxN).1 ht0'
  ·
    intro x hx
    constructor
    · intro hxZ₂
      have hxN := P.Z₂_le_N hxZ₂
      have ha0 : fr₁.a x = 0 := fr₁.a_of_mem_W hxN.2
      have hb0 : fr₁.b x = 0 := fr₁.b_of_mem_V hxN.1
      have hnx : nn x = x := by
        simp only [hnn_def]
        rw [ha0, hb0, hα0, hβ0]
        group
      refine ⟨ha0, hb0, ?_⟩
      show κe.symm (fr₂.c (nn x)) = 0
      rw [hnx, fr₂.c_of_mem_Z hxZ₂, hκe_zero]
    · rintro ⟨ha0, hb0, hw0⟩
      replace ha0 : fr₁.a x = 0 := ha0
      replace hb0 : fr₁.b x = 0 := hb0
      have hxN : x ∈ V ⊓ W :=
        Subgroup.mem_inf.2 ⟨(fr₁.mem_V_iff_b hx).2 hb0, (fr₁.mem_W_iff_a hx).2 ha0⟩
      have hnx : nn x = x := by
        simp only [hnn_def]
        rw [ha0, hb0, hα0, hβ0]
        group
      have hw0' : κe.symm (fr₂.c (nn x)) = 0 := hw0
      rw [hnx] at hw0'
      have h1 : fr₂.c x = 0 := by
        have := congrArg κe hw0'
        rw [Equiv.apply_symm_apply] at this
        rw [this]
        show κ 0 = 0
        exact map_zero κ
      exact (fr₂.c_eq_zero_iff (hNN hxN)).1 h1

end S4Pair

end CFSG.CGT.PushingUpLit.A78S4
