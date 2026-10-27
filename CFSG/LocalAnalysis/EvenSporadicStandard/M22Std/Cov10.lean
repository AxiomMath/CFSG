module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov9

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Swap

variable {L : Type} [Group L] {t : L}

theorem TwFacts.alpha_fix_aux (F : TwFacts L t) (h : IsM22Cover L t) (y : L)
    (hφy : F.φ y = F.z) (hAlsq : ∀ g ∈ F.Al, ∀ p : L, F.φ p = g → p * p = y) (α : L ≃* L)
    (hαt : α t = t) (hαP : ∀ p : L, F.φ p ∈ F.S0 ↔ F.φ (α p) ∈ F.S0) : α y = y := by
  classical
  have hφt : F.φ t = 1 := (F.ker_iff t).2 (Or.inr rfl)
  have hyP : F.φ y ∈ F.S0 := hφy ▸ F.z_mem
  have hαyP : F.φ (α y) ∈ F.S0 := (hαP y).1 hyP
  have hαsymm : α.symm t = t := (α.symm_apply_eq).2 hαt.symm
  have hcomm : ∀ g ∈ F.S0, F.φ (α y) * g = g * F.φ (α y) := by
    intro g hg
    obtain ⟨q, hq⟩ := F.surj g hg
    have hq' : F.φ (α.symm q) ∈ F.S0 := by
      have h0 := (hαP (α.symm q)).2
      rw [MulEquiv.apply_symm_apply] at h0
      exact h0 (hq ▸ hg)
    have h1 : F.φ (y * α.symm q) = F.φ (α.symm q * y) := by
      rw [map_mul, map_mul, hφy]
      exact F.z_central _ hq'
    have h2 : F.φ (y * α.symm q * (α.symm q * y)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    rcases (F.ker_iff _).1 h2 with h3 | h3
    · have h4 : y * α.symm q = α.symm q * y := mul_inv_eq_one.1 h3
      have h5 := congrArg α h4
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h5
      rw [← hq, ← map_mul, ← map_mul, h5]
    · have h4 : y * α.symm q = t * (α.symm q * y) := by
        calc y * α.symm q = (y * α.symm q * (α.symm q * y)⁻¹) * (α.symm q * y) := by group
          _ = t * (α.symm q * y) := by rw [h3]
      have h5 := congrArg α h4
      rw [map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply, hαt] at h5
      rw [← hq, ← map_mul, ← map_mul, h5, map_mul, hφt, one_mul]
  have hαyz : F.φ (α y) = F.z := by
    rcases F.center (F.φ (α y)) hαyP hcomm with h1 | h1
    · exfalso
      have hy1 : y = 1 ∨ y = t := by
        rcases (F.ker_iff _).1 h1 with h2 | h2
        · left
          have h3 := congrArg α.symm h2
          rwa [MulEquiv.symm_apply_apply, map_one] at h3
        · right
          have h3 := congrArg α.symm h2
          rwa [MulEquiv.symm_apply_apply, hαsymm] at h3
      have : F.φ y = 1 := (F.ker_iff y).2 hy1
      exact F.z_ne (hφy ▸ this)
    · exact h1
  have hαy : α y = y ∨ α y = y * t := by
    have h1 : F.φ (y⁻¹ * α y) = 1 := by rw [map_mul, map_inv, hαyz, hφy, inv_mul_cancel]
    rcases (F.ker_iff _).1 h1 with h2 | h2
    · left
      exact (inv_mul_eq_one.1 h2).symm
    · right
      calc α y = y * (y⁻¹ * α y) := by group
        _ = y * t := by rw [h2]
  rcases hαy with h1 | h1
  · exact h1
  · exfalso
    have hex : ∀ g : Equiv.Perm (Fin 22), ∃ p : L, g ∈ F.S0 → F.φ p = g := fun g => by
      by_cases hg : g ∈ F.S0
      · obtain ⟨p, hp⟩ := F.surj g hg
        exact ⟨p, fun _ => hp⟩
      · exact ⟨1, fun h' => absurd h' hg⟩
    choose lift hlift using hex
    have hf : ∀ g ∈ F.Al, F.φ (α (lift g)) ∈ F.Bl := by
      intro g hg
      have hgS := F.Al_sub g hg
      have hp := hlift g hgS
      have hpp : lift g * lift g = y := hAlsq g hg _ hp
      have hfg : F.φ (α (lift g)) * F.φ (α (lift g)) = F.z := by
        have e1 : F.φ (α (lift g)) * F.φ (α (lift g)) = F.φ (α (lift g * lift g)) := by
          simp only [map_mul]
        rw [e1, hpp, h1, map_mul, hφt, mul_one, hφy]
      have hfS : F.φ (α (lift g)) ∈ F.S0 := (hαP (lift g)).1 (by rw [hp]; exact hgS)
      rcases F.roots _ hfS hfg with hA | hB
      · exfalso
        have h2 := hAlsq _ hA (α (lift g)) rfl
        have h2' : α (lift g * lift g) = y := by rw [map_mul]; exact h2
        rw [hpp, h1] at h2'
        have h3 : y * t = y * 1 := by rw [mul_one]; exact h2'
        exact h.t_ne_one (mul_left_cancel h3)
      · exact hB
    have hinj : Set.InjOn (fun g => F.φ (α (lift g))) (F.Al : Set (Equiv.Perm (Fin 22))) := by
      intro g hg g' hg' hgg
      have hg1 := Finset.mem_coe.1 hg
      have hg2 := Finset.mem_coe.1 hg'
      have hgg' : F.φ (α (lift g)) = F.φ (α (lift g')) := hgg
      have h2 : F.φ (α (lift g) * (α (lift g'))⁻¹) = 1 := by
        rw [map_mul, map_inv, hgg', mul_inv_cancel]
      have hl : F.φ (lift g) = F.φ (lift g') := by
        rcases (F.ker_iff _).1 h2 with h3 | h3
        · have h4 : α (lift g) = α (lift g') := mul_inv_eq_one.1 h3
          rw [α.injective h4]
        · have h4 : α (lift g) = α (t * lift g') := by
            have h5 : α (lift g) = t * α (lift g') := by
              calc α (lift g) = (α (lift g) * (α (lift g'))⁻¹) * α (lift g') := by group
                _ = t * α (lift g') := by rw [h3]
            rw [h5, map_mul, hαt]
          rw [α.injective h4, map_mul, hφt, one_mul]
      calc g = F.φ (lift g) := (hlift g (F.Al_sub g hg1)).symm
        _ = F.φ (lift g') := hl
        _ = g' := hlift g' (F.Al_sub g' hg2)
    have hcard := Finset.card_le_card_of_injOn (fun g => F.φ (α (lift g))) hf hinj
    rw [F.Al_card, F.Bl_card] at hcard
    omega

theorem TwFacts.alpha_fix (F : TwFacts L t) (h : IsM22Cover L t) (α : L ≃* L) (hαt : α t = t)
    (hαP : ∀ p : L, F.φ p ∈ F.S0 ↔ F.φ (α p) ∈ F.S0) :
    α (F.w₁ * F.w₁) = F.w₁ * F.w₁ :=
  F.alpha_fix_aux h _ F.φ_sq F.Al_sq α hαt hαP

end Swap

section Main

variable {H : Type} [Group H] [Finite H] {L : Type} [Group L] {t : L}

omit [Finite H] in
theorem twisted_sylow (ι : L →* H) (hι : Function.Injective ι) (hn : ι.range.Normal)
    (ht : ∀ h : H, ι t * h = h * ι t) (hcov : IsM22Cover L t) (F : TwFacts L t)
    (hno : ∀ y : H, y ∉ ι.range → orderOf y ≠ 2) :
    ∃ T : Sylow 2 H,
      (∀ ψ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H), (x : H) = ι t → ψ x = x) ∧
      ∀ u ∈ ι.range, orderOf u = 2 → ∃ k ∈ ι.range, ∃ z ∈ center (T : Subgroup H),
        (z : H) = k⁻¹ * u * k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hφt : F.φ t = 1 := (F.ker_iff t).2 (Or.inr rfl)
  set P₀ : Subgroup L := F.S0.comap F.φ with hP₀
  set P : Subgroup H := P₀.map ι with hP
  have htP₀ : t ∈ P₀ := by
    show F.φ t ∈ F.S0
    rw [hφt]
    exact F.S0.one_mem
  have hS0p : IsPGroup 2 F.S0 := IsPGroup.of_card (n := 7) (by rw [F.card_S0]; norm_num)
  have hker2 : IsPGroup 2 F.φ.ker := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨x, hx⟩
    rcases (F.ker_iff x).1 hx with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [Subgroup.orderOf_mk, pow_one]; exact hcov.orderOf_t⟩
  have hP₀p : IsPGroup 2 P₀ := hS0p.comap_of_ker_isPGroup F.φ hker2
  have hPp : IsPGroup 2 P := hP₀p.map ι
  obtain ⟨T, hPT⟩ := hPp.exists_le_sylow
  have hιP : ∀ l ∈ P₀, ι l ∈ (T : Subgroup H) := fun l hl => hPT ⟨l, hl, rfl⟩
  have htT : ι t ∈ (T : Subgroup H) := hιP t htP₀
  have hTL : ∀ l : L, ι l ∈ (T : Subgroup H) → l ∈ P₀ := by
    set Q₀ : Subgroup L := (T : Subgroup H).comap ι with hQ₀
    have hQp : IsPGroup 2 Q₀ := T.isPGroup'.comap_of_injective ι hι
    have hP₀Q : P₀ ≤ Q₀ := fun l hl => hιP l hl
    have hQm : IsPGroup 2 (Q₀.map F.φ) := hQp.map F.φ
    have hdvd : Nat.card (Q₀.map F.φ) ∣ 443520 := by
      rw [← F.card_range]
      exact Subgroup.card_dvd_of_le (Subgroup.map_le_range F.φ Q₀)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQm
    have hk7 : k ≤ 7 := by
      by_contra hk8
      push Not at hk8
      have h1 : 2 ^ 8 ∣ 2 ^ k := pow_dvd_pow 2 hk8
      rw [← hk] at h1
      have h2 := dvd_trans h1 hdvd
      norm_num at h2
    have hle : F.S0 ≤ Q₀.map F.φ := fun g hg => by
      obtain ⟨x, hx⟩ := F.surj g hg
      exact ⟨x, hP₀Q (show F.φ x ∈ F.S0 from hx ▸ hg), hx⟩
    have heq : F.S0 = Q₀.map F.φ := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hk, F.card_S0]
      calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
        _ = 128 := by norm_num
    intro l hl
    have h1 : F.φ l ∈ Q₀.map F.φ := ⟨l, hl, rfl⟩
    rw [← heq] at h1
    exact h1
  have hinvP : ∀ x : H, x ∈ (T : Subgroup H) → x * x = 1 → ∃ l ∈ P₀, ι l = x := by
    intro x hxT hx2
    by_cases hx1 : x = 1
    · exact ⟨1, P₀.one_mem, by rw [hx1, map_one]⟩
    · have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
      have hxL : x ∈ ι.range := by
        by_contra hxL
        exact hno x hxL hord
      obtain ⟨l, rfl⟩ := hxL
      exact ⟨l, hTL l hxT, rfl⟩
  have hchar : ∀ ψ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H),
      (∃ l ∈ P₀, ι l = (x : H)) → ∃ l' ∈ P₀, ι l' = ((ψ x : (T : Subgroup H)) : H) := by
    set Ω : Set (T : Subgroup H) := {x | x * x = 1} with hΩ
    set W : Subgroup (T : Subgroup H) := Subgroup.closure Ω with hW
    have hWP : W.map (T : Subgroup H).subtype = P := by
      refine le_antisymm ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        refine (Subgroup.closure_le _).2 fun g hg => ?_
        obtain ⟨l, hl, hlg⟩ := hinvP (g : H) g.2 (by
          have := congrArg Subtype.val hg
          simpa using this)
        exact ⟨l, hl, hlg⟩
      · rintro _ ⟨l, hl, rfl⟩
        have hl' : l ∈ Subgroup.closure {p : L | F.φ p ∈ F.S0 ∧ p * p = 1} := by
          rw [F.gen]
          exact hl
        refine Subgroup.closure_induction (p := fun l _ => ι l ∈ W.map (T : Subgroup H).subtype)
          ?_ ?_ ?_ ?_ hl'
        · intro p hp
          refine ⟨⟨ι p, hιP p hp.1⟩, Subgroup.subset_closure ?_, rfl⟩
          show (⟨ι p, hιP p hp.1⟩ : (T : Subgroup H)) * ⟨ι p, hιP p hp.1⟩ = 1
          apply Subtype.ext
          show ι p * ι p = 1
          rw [← map_mul, hp.2, map_one]
        · rw [map_one]
          exact (W.map _).one_mem
        · intro a b _ _ ha hb
          rw [map_mul]
          exact (W.map _).mul_mem ha hb
        · intro a _ ha
          rw [map_inv]
          exact (W.map _).inv_mem ha
    have hWψ : ∀ ψ : MulAut (T : Subgroup H), W ≤ W.comap ψ.toMonoidHom := by
      intro ψ
      refine (Subgroup.closure_le _).2 fun g hg => ?_
      refine Subgroup.subset_closure ?_
      show ψ g * ψ g = 1
      rw [← map_mul, show g * g = 1 from hg, map_one]
    intro ψ x ⟨l, hl, hlx⟩
    have hxW : x ∈ W := by
      have h1 : (x : H) ∈ W.map (T : Subgroup H).subtype := by
        rw [hWP]
        exact ⟨l, hl, hlx⟩
      obtain ⟨w, hw, hwx⟩ := h1
      have : w = x := Subtype.ext hwx
      rwa [← this]
    have h1 : ψ x ∈ W := hWψ ψ hxW
    have h2 : ((ψ x : (T : Subgroup H)) : H) ∈ P := by
      rw [← hWP]
      exact ⟨ψ x, h1, rfl⟩
    obtain ⟨l', hl', hl'x⟩ := h2
    exact ⟨l', hl', hl'x⟩
  refine ⟨T, ?_, ?_⟩
  ·
    intro ψ x hx
    have hxe : x = ⟨ι t, htT⟩ := Subtype.ext hx
    have hxx : x * x = 1 := by
      apply Subtype.ext
      show (x : H) * (x : H) = 1
      rw [hx, ← map_mul, hcov.mul_self_t, map_one]
    have hcc : ψ x * ψ x = 1 := by rw [← map_mul, hxx, map_one]
    have hcentral : ∀ y : (T : Subgroup H), ψ x * y = y * ψ x := by
      intro y
      obtain ⟨y', rfl⟩ := ψ.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (x : H) * (y' : H) = (y' : H) * (x : H)
      rw [hx]
      exact ht _
    obtain ⟨l, hlP, hcl⟩ := hinvP ((ψ x : (T : Subgroup H)) : H) (ψ x).2
      (by have := congrArg Subtype.val hcc; simpa using this)
    have hφl : F.φ l = 1 ∨ F.φ l = F.z := by
      refine F.center (F.φ l) hlP fun g hg => ?_
      obtain ⟨q, hq⟩ := F.surj g hg
      have hqP : q ∈ P₀ := show F.φ q ∈ F.S0 from hq ▸ hg
      have hcomm := hcentral ⟨ι q, hιP q hqP⟩
      have h1 : ι (l * q) = ι (q * l) := by
        rw [map_mul, map_mul, hcl]
        exact (congrArg Subtype.val hcomm)
      have h2 := hι h1
      rw [← hq, ← map_mul, ← map_mul, h2]
    rcases hφl with h1 | h1
    · rcases (F.ker_iff l).1 h1 with h2 | h2
      · exfalso
        have h3 : ψ x = 1 := Subtype.ext (by rw [← hcl, h2, map_one]; rfl)
        have h4 : x = 1 := by
          have := congrArg ψ.symm h3
          rwa [MulEquiv.symm_apply_apply, map_one] at this
        have h5 : t = 1 := hι (by
          have := congrArg Subtype.val h4
          simpa [hx] using this)
        exact hcov.t_ne_one h5
      · exact Subtype.ext (by rw [← hcl, h2]; exact hx.symm)
    · exfalso
      have hlw : ∃ w : L, F.φ w ∈ F.S0 ∧ l = w * w := by
        have h2 : F.φ ((F.w₁ * F.w₁)⁻¹ * l) = 1 := by
          rw [map_mul, map_inv, F.φ_sq, h1, inv_mul_cancel]
        rcases (F.ker_iff _).1 h2 with h3 | h3
        · exact ⟨F.w₁, F.w₁_mem, (inv_mul_eq_one.1 h3).symm⟩
        · refine ⟨F.w₂, F.w₂_mem, ?_⟩
          have h4 : l = F.w₁ * F.w₁ * t := by
            calc l = (F.w₁ * F.w₁) * ((F.w₁ * F.w₁)⁻¹ * l) := by group
              _ = F.w₁ * F.w₁ * t := by rw [h3]
          rw [h4, F.w_rel, mul_assoc, mul_assoc, hcov.mul_self_t, mul_one]
      obtain ⟨w, hwS, rfl⟩ := hlw
      have hwP : w ∈ P₀ := hwS
      set wT : (T : Subgroup H) := ⟨ι w, hιP w hwP⟩ with hwT
      have hcw : ψ x = wT * wT := by
        apply Subtype.ext
        rw [← hcl]
        show ι (w * w) = ι w * ι w
        rw [map_mul]
      have hu : ψ.symm wT * ψ.symm wT = x := by
        rw [← map_mul, ← hcw, MulEquiv.symm_apply_apply]
      obtain ⟨l', hl', hl'u⟩ := hchar ψ.symm wT ⟨w, hwP, rfl⟩
      apply F.not_sq l'
      apply hι
      rw [map_mul, hl'u, ← Subgroup.coe_mul, hu, hx]
  ·
    have hnorm : ∀ (x : H) (l : L), ∃ l' : L, ι l' = x * ι l * x⁻¹ := fun x l => by
      obtain ⟨l', hl'⟩ := hn.conj_mem (ι l) ⟨l, rfl⟩ x
      exact ⟨l', hl'⟩
    have hcentral_y : ∀ x : H, x ∈ (T : Subgroup H) →
        x * ι (F.w₁ * F.w₁) = ι (F.w₁ * F.w₁) * x := by
      intro x hxT
      choose a ha using hnorm x
      choose b hb using hnorm x⁻¹
      let α : L ≃* L :=
        { toFun := a
          invFun := b
          left_inv := fun l => hι (by rw [hb, ha]; group)
          right_inv := fun l => hι (by rw [ha, hb]; group)
          map_mul' := fun l l' => hι (by simp only [map_mul, ha]; group) }
      have hαa : ∀ l, ι (α l) = x * ι l * x⁻¹ := ha
      have hαt : α t = t := hι (by
        rw [hαa]
        calc x * ι t * x⁻¹ = (ι t * x) * x⁻¹ := by rw [ht x]
          _ = ι t := mul_inv_cancel_right _ _)
      have hαP : ∀ p : L, F.φ p ∈ F.S0 ↔ F.φ (α p) ∈ F.S0 := by
        intro p
        have h1 : F.φ p ∈ F.S0 ↔ ι p ∈ (T : Subgroup H) := ⟨fun hp => hιP p hp, fun hp => hTL p hp⟩
        have h2 : F.φ (α p) ∈ F.S0 ↔ ι (α p) ∈ (T : Subgroup H) :=
          ⟨fun hp => hιP _ hp, fun hp => hTL _ hp⟩
        rw [h1, h2, hαa]
        constructor
        · intro hp
          exact (T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem hxT hp)
            ((T : Subgroup H).inv_mem hxT)
        · intro hp
          have h3 := (T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem
            ((T : Subgroup H).inv_mem hxT) hp) hxT
          simpa [mul_assoc] using h3
      have h4 := congrArg ι (F.alpha_fix hcov α hαt hαP)
      rw [hαa] at h4
      calc x * ι (F.w₁ * F.w₁) = (x * ι (F.w₁ * F.w₁) * x⁻¹) * x := by group
        _ = ι (F.w₁ * F.w₁) * x := by rw [h4]
    rintro u ⟨u₀, rfl⟩ hu2
    by_cases hut : u₀ = t
    · rw [hut]
      exact ⟨1, ι.range.one_mem, ⟨ι t, htT⟩,
        Subgroup.mem_center_iff.2 fun g => Subtype.ext (ht g).symm, by simp⟩
    · have hu0sq : u₀ * u₀ = 1 := by
        apply hι
        rw [map_mul, map_one]
        have h1 : ι u₀ ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one _
        rwa [sq] at h1
      have hφu : F.φ u₀ ≠ 1 := by
        intro h1
        rcases (F.ker_iff u₀).1 h1 with h2 | h2
        · rw [h2, map_one, orderOf_one] at hu2
          exact absurd hu2 (by decide)
        · exact hut h2
      obtain ⟨c, hc⟩ := F.conj u₀ hu0sq hφu
      have key : ∀ y : L, F.φ y ∈ F.S0 → (∀ x : H, x ∈ (T : Subgroup H) → x * ι y = ι y * x) →
          u₀ = c * y * c⁻¹ → ∃ k ∈ ι.range, ∃ z ∈ center (T : Subgroup H),
            (z : H) = k⁻¹ * ι u₀ * k := by
        intro y hyS hycen hu₁
        refine ⟨ι c, ⟨c, rfl⟩, ⟨ι y, hιP y hyS⟩,
          Subgroup.mem_center_iff.2 fun g => Subtype.ext (hycen g g.2), ?_⟩
        show ι y = (ι c)⁻¹ * ι u₀ * ι c
        rw [hu₁]
        simp only [map_mul, map_inv]
        group
      rcases hc with hc | hc
      · exact key (F.w₁ * F.w₁) (by rw [F.φ_sq]; exact F.z_mem) hcentral_y hc
      · refine key (F.w₂ * F.w₂) (by rw [map_mul]; exact F.S0.mul_mem F.w₂_mem F.w₂_mem) ?_ hc
        intro x hxT
        have h1 : F.w₂ * F.w₂ = F.w₁ * F.w₁ * t := by
          rw [F.w_rel, mul_assoc, hcov.mul_self_t, mul_one]
        rw [h1, map_mul]
        calc x * (ι (F.w₁ * F.w₁) * ι t) = (x * ι (F.w₁ * F.w₁)) * ι t := by rw [mul_assoc]
          _ = (ι (F.w₁ * F.w₁) * x) * ι t := by rw [hcentral_y x hxT]
          _ = ι (F.w₁ * F.w₁) * (x * ι t) := by rw [mul_assoc]
          _ = ι (F.w₁ * F.w₁) * (ι t * x) := by rw [ht x]
          _ = ι (F.w₁ * F.w₁) * ι t * x := by rw [mul_assoc]

end Main

end CFSG.EvenSporadicStandard.M22Std
