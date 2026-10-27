module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsNormal

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

section Generic

variable {G : Type} [Group G]

theorem A6Final.mem_normalizer_conjugate_of {A : Subgroup G} {x g : G}
    (h : x * g * x⁻¹ ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer ((CFSG.conjugate A x : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff]
  have e : x * (g * y * g⁻¹) * x⁻¹ = (x * g * x⁻¹) * (x * y * x⁻¹) * (x * g * x⁻¹)⁻¹ := by group
  rw [e]
  exact h (x * y * x⁻¹)

theorem closed_sup_of {X Y : Subgroup G} {g : G} (hX : ∀ y ∈ X, g * y * g⁻¹ ∈ X ⊔ Y)
    (hY : ∀ y ∈ Y, g * y * g⁻¹ ∈ X ⊔ Y) : ∀ y ∈ X ⊔ Y, g * y * g⁻¹ ∈ X ⊔ Y := by
  intro y hy
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hX y hy
    · exact hY y hy
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact (X ⊔ Y).mul_mem ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact (X ⊔ Y).inv_mem ha

theorem mem_normalizer_of_conj_mem [Finite G] {E : Subgroup G} {g : G}
    (h : ∀ y ∈ E, g * y * g⁻¹ ∈ E) : g ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  let φ : ↥E → ↥E := fun z => ⟨g * z * g⁻¹, h z z.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    apply Subtype.ext
    simpa using h1
  obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.mp hinj ⟨g * y * g⁻¹, hy⟩
  have h1 : g * (z : G) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hz
  have : (z : G) = y := by simpa using h1
  rw [← this]
  exact z.2

end Generic

section Final

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

structure FinalCtx (N : Notation25 hs) (t zK : G) (D : A6Datum N) : Prop where
  hK0 : N.K0 = N.K
  hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)
  hf : Facts2511 N t zK
  h254 : Facts254 N
  h258 : Facts258 N
  hxt : N.x⁻¹ * t * N.x = zK
  hz : N.z = t * zK
  hΦzK : D.Φ zK = zb
  hinv : ∀ i ∈ N.SC, i ≠ 1 → i * i = 1 → i = t

variable {N : Notation25 hs} {t zK : G} {D : A6Datum N}

theorem FinalCtx.hsimple (C : FinalCtx N t zK D) : IsSimpleGroup ↥N.K := C.h258.simple

theorem FinalCtx.hZK (C : FinalCtx N t zK D) :
    ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun _ hx hc =>
  N.center_K_trivial C.hsimple hx hc

theorem FinalCtx.t_comm (C : FinalCtx N t zK D) {s : G} (hs' : s ∈ N.S) : s * t = t * s :=
  Subgroup.mem_centralizer_iff.mp C.hf.t_mem_center.2 s hs'

theorem FinalCtx.zK_comm (C : FinalCtx N t zK D) {s : G} (hs' : s ∈ N.S) : s * zK = zK * s :=
  Subgroup.mem_centralizer_iff.mp C.hf.zK_mem_center.2 s hs'

theorem FinalCtx.x_t (C : FinalCtx N t zK D) : N.x * t * N.x⁻¹ = zK := by
  have h2 : N.x * N.x ∈ N.S := by simpa [sq] using N.x_sq
  have h := C.zK_comm h2
  calc N.x * t * N.x⁻¹ = (N.x * N.x) * (N.x⁻¹ * t * N.x) * (N.x * N.x)⁻¹ := by group
    _ = (N.x * N.x) * zK * (N.x * N.x)⁻¹ := by rw [C.hxt]
    _ = zK := by rw [h]; group

theorem FinalCtx.zK_x (C : FinalCtx N t zK D) : N.x⁻¹ * zK * N.x = t := by
  have h2 : N.x * N.x ∈ N.S := by simpa [sq] using N.x_sq
  have h := C.t_comm h2
  calc N.x⁻¹ * zK * N.x = N.x⁻¹ * (N.x⁻¹ * t * N.x) * N.x := by rw [C.hxt]
    _ = (N.x * N.x)⁻¹ * t * (N.x * N.x) := by group
    _ = t := by rw [mul_assoc, ← h]; group

theorem FinalCtx.x_zK (C : FinalCtx N t zK D) : N.x * zK * N.x⁻¹ = t := by
  have h2 : N.x * N.x ∈ N.S := by simpa [sq] using N.x_sq
  have h := C.t_comm h2
  calc N.x * zK * N.x⁻¹ = (N.x * N.x) * (N.x⁻¹ * zK * N.x) * (N.x * N.x)⁻¹ := by group
    _ = (N.x * N.x) * t * (N.x * N.x)⁻¹ := by rw [C.zK_x]
    _ = t := by rw [h]; group

theorem FinalCtx.SKx_le_S (_C : FinalCtx N t zK D) {b : G} (hb : b ∈ CFSG.conjugate N.SK N.x) :
    b ∈ N.S := by
  have h1 : N.x * b * N.x⁻¹ ∈ N.SK := BenderBranch.mem_conjugate_iff.mp hb
  have h2 := N.x_conj_S' (N.SK_le_S h1)
  simpa [mul_assoc] using h2

theorem FinalCtx.S_le_normalizer_SKx (C : FinalCtx N t zK D) :
    N.S ≤ Subgroup.normalizer ((CFSG.conjugate N.SK N.x : Subgroup G) : Set G) := fun _ hs' =>
  A6Final.mem_normalizer_conjugate_of (N.S_le_normalizer_SK C.hKH (N.x_conj_S hs'))

theorem FinalCtx.SK_inf_SKx (C : FinalCtx N t zK D) :
    N.SK ⊓ CFSG.conjugate N.SK N.x = ⊥ := by
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  by_contra hne
  have hWS : N.SK ⊓ CFSG.conjugate N.SK N.x ≤ N.S := inf_le_left.trans N.SK_le_S
  have hSW := N.S_le_normalizer_SK_inf C.hKH C.S_le_normalizer_SKx
  have hne' := inf_centralizer_ne_bot_of_normalizes hS2 hWS hSW hne
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
  have hw1' : w ≠ 1 := fun e => hw1 (Subtype.ext e)
  have hwS : w ∈ N.S := hWS hw.1
  have hwZ : w ∈ centerOf N.S ⊓ N.SK := ⟨⟨hwS, hw.2⟩, hw.1.1⟩
  rw [N.center_inf_SK_eq C.hK0 C.h258 C.hf] at hwZ
  rcases mem_zpowers_involution C.hf.zK_sq hwZ with h1 | h1
  · exact hw1' h1
  · have hwx : w ∈ CFSG.conjugate N.SK N.x := hw.1.2
    rw [BenderBranch.mem_conjugate_iff, h1, C.x_zK] at hwx
    have htK : t ∈ N.K := hwx.2
    have h3 : t ∈ N.K0 ⊓ N.SC := ⟨C.hK0 ▸ htK, C.hf.t_mem⟩
    rw [C.h258.K0_inf_SC, Subgroup.mem_bot] at h3
    exact C.hf.t_ne_one h3

theorem FinalCtx.comm_SK_SKx (C : FinalCtx N t zK D) :
    ∀ a ∈ N.SK, ∀ b ∈ CFSG.conjugate N.SK N.x, a * b = b * a := by
  intro a ha b hb
  have haS : a ∈ N.S := N.SK_le_S ha
  have hbS : b ∈ N.S := C.SKx_le_S hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ N.SK :=
    Subgroup.le_normalizer_iff.mp (N.S_le_normalizer_SK C.hKH) b hbS a⁻¹ (N.SK.inv_mem ha)
  have h2 : a * b * a⁻¹ ∈ CFSG.conjugate N.SK N.x :=
    Subgroup.le_normalizer_iff.mp C.S_le_normalizer_SKx a haS b hb
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ N.SK ⊓ CFSG.conjugate N.SK N.x := by
    refine ⟨?_, (CFSG.conjugate N.SK N.x).mul_mem h2 ((CFSG.conjugate N.SK N.x).inv_mem hb)⟩
    have := N.SK.mul_mem ha h1
    simpa [mul_assoc] using this
  rw [C.SK_inf_SKx, Subgroup.mem_bot] at h3
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

theorem FinalCtx.inE4_of_SKx (C : FinalCtx N t zK D) {f : G}
    (hf : f ∈ CFSG.conjugate N.SK N.x) : InE4 (D.Φ f) := by
  refine ⟨D.S_mem f (C.SKx_le_S hf), fun d hdP hdpsl => ?_⟩
  obtain ⟨a, haSK, rfl⟩ := D.exists_mem_SK C.hKH C.h254 C.hsimple hdP hdpsl
  have haH := N.S_le_H (N.SK_le_S haSK)
  have hfH := N.S_le_H (C.SKx_le_S hf)
  have h1 := C.comm_SK_SKx a haSK f hf
  calc D.Φ f * D.Φ a = D.Φ (f * a) := (D.mul f hfH a haH).symm
    _ = D.Φ (a * f) := by rw [h1]
    _ = D.Φ a * D.Φ f := D.mul a haH f hfH

theorem FinalCtx.t_not_mem_K (C : FinalCtx N t zK D) : t ∉ N.K := by
  intro htK
  have h3 : t ∈ N.K0 ⊓ N.SC := ⟨C.hK0 ▸ htK, C.hf.t_mem⟩
  rw [C.h258.K0_inf_SC, Subgroup.mem_bot] at h3
  exact C.hf.t_ne_one h3

theorem FinalCtx.refl_image (C : FinalCtx N t zK D) {b : G} (hb : b ∈ N.SK)
    (hbr : IsRefl (D.Φ b)) :
    N.x⁻¹ * b * N.x ∈ CFSG.conjugate N.SK N.x ∧ (N.x⁻¹ * b * N.x) * (N.x⁻¹ * b * N.x) = 1 ∧
      D.Φ (N.x⁻¹ * b * N.x) ≠ 1 ∧ D.Φ (N.x⁻¹ * b * N.x) ≠ zb ∧
        InE4 (D.Φ (N.x⁻¹ * b * N.x)) := by
  set f := N.x⁻¹ * b * N.x with hfdef
  have hbK : b ∈ N.K := hb.2
  have hbH : b ∈ N.H := N.K_le_H hbK
  have hb2 : b * b = 1 := by
    apply D.inj_K C.hsimple (N.K.mul_mem hbK hbK) N.K.one_mem
    rw [D.mul b hbH b hbH, hbr.2.2.2.2, D.Φ_one]
  have hfmem : f ∈ CFSG.conjugate N.SK N.x := by
    rw [BenderBranch.mem_conjugate_iff]
    have : N.x * f * N.x⁻¹ = b := by rw [hfdef]; group
    rw [this]; exact hb
  have hf2 : f * f = 1 := by
    have : f * f = N.x⁻¹ * (b * b) * N.x := by rw [hfdef]; group
    rw [this, hb2]; group
  have hfS : f ∈ N.S := C.SKx_le_S hfmem
  have hbf : b = N.x * f * N.x⁻¹ := by rw [hfdef]; group
  have hf1 : f ≠ 1 := by
    intro h1
    have : b = 1 := by rw [hbf, h1]; group
    exact hbr.2.2.1 (by rw [this, D.Φ_one])
  refine ⟨hfmem, hf2, ?_, ?_, C.inE4_of_SKx hfmem⟩
  · intro h1
    have hfSC : f ∈ N.SC := D.mem_SC_of_Φ_eq_one C.hK0 hfS h1
    have hft : f = t := C.hinv f hfSC hf1 hf2
    have : b = zK := by rw [hbf, hft, C.x_t]
    exact hbr.2.2.2.1 (by rw [this, C.hΦzK])
  · intro hz
    have hzKS : zK ∈ N.S := N.SK_le_S (C.hf.zK_mem_SK C.hK0)
    have hzKK : zK ∈ N.K := (C.hf.zK_mem_SK C.hK0).2
    have hc : zK⁻¹ * f ∈ N.SC := D.inv_mul_mem_SC C.hK0 hzKS hfS (by rw [C.hΦzK, hz])
    set c := zK⁻¹ * f with hcdef
    have hcomm : zK * c = c * zK :=
      Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hc) zK (C.hK0 ▸ hzKK)
    have hfc : f = zK * c := by rw [hcdef]; group
    have hcc : c * c = 1 := by
      have h1 : f * f = (zK * zK) * (c * c) := by
        rw [hfc]
        calc zK * c * (zK * c) = zK * (c * zK) * c := by group
          _ = zK * (zK * c) * c := by rw [← hcomm]
          _ = (zK * zK) * (c * c) := by group
      rw [hf2, C.hf.zK_sq, one_mul] at h1
      exact h1.symm
    by_cases hc1 : c = 1
    · apply C.t_not_mem_K
      have : b = t := by rw [hbf, hfc, hc1, mul_one, C.x_zK]
      rw [← this]; exact hbK
    · have hct : c = t := C.hinv c hc hc1 hcc
      apply C.t_not_mem_K
      have hb' : b = t * zK := by
        calc b = N.x * (zK * t) * N.x⁻¹ := by rw [hbf, hfc, hct]
          _ = (N.x * zK * N.x⁻¹) * (N.x * t * N.x⁻¹) := by group
          _ = t * zK := by rw [C.x_zK, C.x_t]
      have : t = b * zK⁻¹ := by rw [hb']; group
      rw [this]
      exact N.K.mul_mem hbK (N.K.inv_mem hzKK)

theorem ncard_D : Set.ncard {x : P10 | x ∈ P0 ∧ x ∈ A6Models.psl29} = 8 := by
  have hnd : Core.dLit.Nodup := by rw [Core.d_eq]; exact Core.p0_nodup.filter _
  have hlen : Core.dLit.length = 8 := by decide +kernel
  rw [← hlen]
  exact ncard_eq_of_code_mem hnd (fun x => mem_D_iff x) (fun c hc => by
    obtain ⟨x, hxP, hxpsl, rfl⟩ := exists_D_of_code hc
    exact ⟨x, ⟨hxP, hxpsl⟩, rfl⟩)

theorem FinalCtx.card_SK_le (C : FinalCtx N t zK D) : Nat.card ↥N.SK ≤ 8 := by
  have hinj : Function.Injective (fun a : ↥N.SK =>
      (⟨D.Φ (a : G), D.S_mem a (N.SK_le_S a.2), D.K_mem a a.2.2⟩ :
        {x : P10 | x ∈ P0 ∧ x ∈ A6Models.psl29})) := by
    intro a b h
    apply Subtype.ext
    have h' : D.Φ (a : G) = D.Φ (b : G) := congrArg Subtype.val h
    exact D.inj_K C.hsimple a.2.2 b.2.2 h'
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_coe_set_eq, ncard_D] at h1
  exact h1

theorem four_inj {τ τ' : P10} (h1 : τ ≠ 1) (h1' : τ' ≠ 1) (h2 : τ * τ = 1) (hne : τ ≠ τ') :
    Function.Injective ![1, τ, τ', τ * τ'] := by
  have hne1 : τ * τ' ≠ 1 := by
    intro h
    apply hne
    have : τ' = τ⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right h2).symm
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;>
    first
    | exact absurd h h1 | exact absurd h.symm h1 | exact absurd h h1' | exact absurd h.symm h1'
    | exact absurd h hne | exact absurd h.symm hne | exact absurd h hne1 | exact absurd h.symm hne1

theorem FinalCtx.SKx_inf_SC (C : FinalCtx N t zK D) {e : G} (he : e ∈ N.SK)
    (her : IsRefl (D.Φ e)) :
    ∀ w ∈ CFSG.conjugate N.SK N.x, w ∈ N.SC → w = 1 ∨ w = t := by
  obtain ⟨hf1mem, hf1sq, hf1ne, hf1zb, hf1E4⟩ := C.refl_image he her
  set f₁ : G := N.x⁻¹ * e * N.x with hf₁
  set τ : P10 := D.Φ f₁ with hτ
  have hτP : τ ∈ P0 := hf1E4.1
  have hτsq : τ * τ = 1 := P0_sq_of_centralizes_D hτP hf1E4.2
  obtain ⟨p, hpP, hpτ⟩ : ∃ p ∈ P0, ¬ τ * p = p * τ := by
    by_contra hcon
    push Not at hcon
    rcases center_P0 hτP hcon with h | h
    · exact hf1ne h
    · exact hf1zb h
  obtain ⟨sp, hspS, hspΦ⟩ := D.S_surj p hpP
  have hspH : sp ∈ N.H := N.S_le_H hspS
  have hf₁S : f₁ ∈ N.S := C.SKx_le_S hf1mem
  have hf₁H : f₁ ∈ N.H := N.S_le_H hf₁S
  set f₂ : G := sp * f₁ * sp⁻¹ with hf₂
  have hf₂mem : f₂ ∈ CFSG.conjugate N.SK N.x :=
    Subgroup.le_normalizer_iff.mp C.S_le_normalizer_SKx sp hspS f₁ hf1mem
  have hf₂H : f₂ ∈ N.H := N.S_le_H (C.SKx_le_S hf₂mem)
  have hf₂Φ : D.Φ f₂ = p * τ * p⁻¹ := by rw [hf₂, D.Φ_conj hspH hf₁H, hspΦ]
  set τ' : P10 := p * τ * p⁻¹ with hτ'
  have hτ'1 : τ' ≠ 1 := by
    intro h
    apply hf1ne
    have : τ = p⁻¹ * (p * τ * p⁻¹) * p := by group
    rw [this, ← hτ', h]; group
  have hττ' : τ ≠ τ' := by
    intro h
    apply hpτ
    calc τ * p = (p * τ * p⁻¹) * p := by rw [← hτ', ← h]
      _ = p * τ := by group
  let g : Fin 4 → G := ![1, f₁, f₂, f₁ * f₂]
  let v : Fin 4 → P10 := ![1, τ, τ', τ * τ']
  have hgmem : ∀ i, g i ∈ CFSG.conjugate N.SK N.x := by
    intro i
    fin_cases i
    · exact (CFSG.conjugate N.SK N.x).one_mem
    · exact hf1mem
    · exact hf₂mem
    · exact (CFSG.conjugate N.SK N.x).mul_mem hf1mem hf₂mem
  have hgH : ∀ i, g i ∈ N.H := fun i => N.S_le_H (C.SKx_le_S (hgmem i))
  have hgΦ : ∀ i, D.Φ (g i) = v i := by
    intro i
    fin_cases i
    · exact D.Φ_one
    · rfl
    · exact hf₂Φ
    · show D.Φ (f₁ * f₂) = τ * τ'
      rw [D.mul f₁ hf₁H f₂ hf₂H, hf₂Φ]
  have hvinj : Function.Injective v := four_inj hf1ne hτ'1 hτsq hττ'
  set B' : Subgroup G := CFSG.conjugate N.SK N.x ⊓ N.SC with hB'
  have hcount : Nat.card (Fin 4 × ↥B') ≤ Nat.card ↥(CFSG.conjugate N.SK N.x) := by
    refine Nat.card_le_card_of_injective
      (fun q => (⟨(q.2 : G) * g q.1, (CFSG.conjugate N.SK N.x).mul_mem q.2.2.1 (hgmem q.1)⟩ :
        ↥(CFSG.conjugate N.SK N.x))) ?_
    rintro ⟨i, w⟩ ⟨j, w'⟩ h
    have h1 : (w : G) * g i = (w' : G) * g j := congrArg Subtype.val h
    have hwH : (w : G) ∈ N.H := N.S_le_H (C.SKx_le_S w.2.1)
    have hw'H : (w' : G) ∈ N.H := N.S_le_H (C.SKx_le_S w'.2.1)
    have hwΦ : D.Φ (w : G) = 1 := D.Φ_eq_one_of_mem_SC C.hK0 w.2.2
    have hw'Φ : D.Φ (w' : G) = 1 := D.Φ_eq_one_of_mem_SC C.hK0 w'.2.2
    have hΦeq : D.Φ (g i) = D.Φ (g j) := by
      have := congrArg D.Φ h1
      rwa [D.mul _ hwH _ (hgH i), D.mul _ hw'H _ (hgH j), hwΦ, hw'Φ, one_mul, one_mul] at this
    have hij : i = j := hvinj (by rw [← hgΦ, ← hgΦ]; exact hΦeq)
    subst hij
    have : (w : G) = w' := mul_right_cancel h1
    rw [Subtype.ext this]
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
    show Nat.card ↥(CFSG.conjugate N.SK N.x) = Nat.card ↥N.SK from card_conjugate _ _] at hcount
  have hB'2 : Nat.card ↥B' ≤ 2 := by
    have := C.card_SK_le
    omega
  intro w hw hwC
  by_contra hcon
  push Not at hcon
  have htx : t ∈ CFSG.conjugate N.SK N.x := by
    rw [BenderBranch.mem_conjugate_iff, C.x_t]
    exact C.hf.zK_mem_SK C.hK0
  let h3 : Fin 3 → ↥B' := ![⟨1, B'.one_mem⟩, ⟨t, ⟨htx, C.hf.t_mem⟩⟩, ⟨w, ⟨hw, hwC⟩⟩]
  have hinj3 : Function.Injective h3 := by
    intro i j h
    have h' : ((h3 i : ↥B') : G) = ((h3 j : ↥B') : G) := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> simp [h3] at h' ⊢ <;>
      first
      | exact absurd h' C.hf.t_ne_one | exact absurd h'.symm C.hf.t_ne_one
      | exact absurd h' hcon.1 | exact absurd h'.symm hcon.1
      | exact absurd h' hcon.2 | exact absurd h'.symm hcon.2
  have := Nat.card_le_card_of_injective _ hinj3
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this
  omega

structure FinalE (C : FinalCtx N t zK D) (E : Subgroup G) (e : G) : Prop where
  hEK : E ≤ N.SK
  hzKE : zK ∈ E
  heE : e ∈ E
  hrefl : IsRefl (D.Φ e)
  hEel : ∀ y ∈ E, y = 1 ∨ y = zK ∨ y = e ∨ y = e * zK

theorem FinalCtx.klein_of_mem_E {E : Subgroup G} {e : G} (C : FinalCtx N t zK D)
    (hE : FinalE C E e) {y : G} (hy : y ∈ E) : KleinMem (D.Φ e) (D.Φ y) := by
  have hzKH : zK ∈ N.H := N.S_le_H (N.SK_le_S (C.hf.zK_mem_SK C.hK0))
  have heH : e ∈ N.H := N.S_le_H (N.SK_le_S (hE.hEK hE.heE))
  rcases hE.hEel y hy with rfl | rfl | rfl | rfl
  · exact Or.inl D.Φ_one
  · exact Or.inr (Or.inl C.hΦzK)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (by rw [D.mul e heH zK hzKH, C.hΦzK])))

theorem FinalCtx.exists_E_of_klein {E : Subgroup G} {e : G} (C : FinalCtx N t zK D)
    (hE : FinalE C E e) {ε : P10} (hε : KleinMem (D.Φ e) ε) : ∃ y ∈ E, D.Φ y = ε := by
  have hzKH : zK ∈ N.H := N.S_le_H (N.SK_le_S (C.hf.zK_mem_SK C.hK0))
  have heH : e ∈ N.H := N.S_le_H (N.SK_le_S (hE.hEK hE.heE))
  rcases hε with rfl | rfl | rfl | rfl
  · exact ⟨1, E.one_mem, D.Φ_one⟩
  · exact ⟨zK, hE.hzKE, C.hΦzK⟩
  · exact ⟨e, hE.heE, rfl⟩
  · exact ⟨e * zK, E.mul_mem hE.heE hE.hzKE, by rw [D.mul e heH zK hzKH, C.hΦzK]⟩

theorem FinalCtx.normKlein_of_normalizes {E : Subgroup G} {e : G} (C : FinalCtx N t zK D)
    (hE : FinalE C E e) {h : G} (hhH : h ∈ N.H) (hhE : h ∈ Subgroup.normalizer (E : Set G)) :
    NormKlein (D.Φ e) (D.Φ h) := by
  intro ε hε
  obtain ⟨y, hyE, rfl⟩ := C.exists_E_of_klein hE hε
  have hyH : y ∈ N.H := N.S_le_H (N.SK_le_S (hE.hEK hyE))
  have hy' : h * y * h⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hhE y).mp hyE
  have hy'H : h * y * h⁻¹ ∈ N.H := N.S_le_H (N.SK_le_S (hE.hEK hy'))
  refine ⟨D.Φ (h * y * h⁻¹), C.klein_of_mem_E hE hy', ?_⟩
  rw [← D.mul h hhH y hyH, ← D.mul _ hy'H h hhH]
  congr 1
  group

theorem FinalCtx.mem_conj_E {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e) :
    N.x⁻¹ * e * N.x ∈ CFSG.conjugate E N.x ∧ t ∈ CFSG.conjugate E N.x := by
  refine ⟨?_, ?_⟩
  · rw [BenderBranch.mem_conjugate_iff]
    have : N.x * (N.x⁻¹ * e * N.x) * N.x⁻¹ = e := by group
    rw [this]; exact hE.heE
  · rw [BenderBranch.mem_conjugate_iff, C.x_t]
    exact hE.hzKE

theorem FinalCtx.normS_conj {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    {s : G} (hsS : s ∈ N.S) (hsE : s ∈ Subgroup.normalizer (E : Set G)) :
    ∀ g ∈ CFSG.conjugate E N.x, s * g * s⁻¹ ∈ CFSG.conjugate E N.x := by
  have heSK : e ∈ N.SK := hE.hEK hE.heE
  have hsH : s ∈ N.H := N.S_le_H hsS
  obtain ⟨hf1mem, hf1sq, hf1ne, hf1zb, hf1E4⟩ := C.refl_image heSK hE.hrefl
  obtain ⟨hf1E, htE⟩ := C.mem_conj_E hE
  set f₁ : G := N.x⁻¹ * e * N.x with hf₁
  have hf₁S : f₁ ∈ N.S := C.SKx_le_S hf1mem
  have hf₁H : f₁ ∈ N.H := N.S_le_H hf₁S
  have hstar : s * f₁ * s⁻¹ ∈ CFSG.conjugate E N.x := by
    have hf'mem : s * f₁ * s⁻¹ ∈ CFSG.conjugate N.SK N.x :=
      Subgroup.le_normalizer_iff.mp C.S_le_normalizer_SKx s hsS f₁ hf1mem
    have hf'S := C.SKx_le_S hf'mem
    have hsΦ : D.Φ s * D.Φ f₁ = D.Φ f₁ * D.Φ s :=
      norm_comm_e4 hE.hrefl (D.S_mem s hsS) (C.normKlein_of_normalizes hE hsH hsE) hf1E4
    have hΦf' : D.Φ f₁ = D.Φ (s * f₁ * s⁻¹) := by
      rw [D.Φ_conj hsH hf₁H, hsΦ]
      group
    have hδ : f₁⁻¹ * (s * f₁ * s⁻¹) ∈ N.SC := D.inv_mul_mem_SC C.hK0 hf₁S hf'S hΦf'
    have hδx : f₁⁻¹ * (s * f₁ * s⁻¹) ∈ CFSG.conjugate N.SK N.x :=
      (CFSG.conjugate N.SK N.x).mul_mem ((CFSG.conjugate N.SK N.x).inv_mem hf1mem) hf'mem
    have hfeq : s * f₁ * s⁻¹ = f₁ * (f₁⁻¹ * (s * f₁ * s⁻¹)) := by group
    rcases C.SKx_inf_SC heSK hE.hrefl _ hδx hδ with h1 | h1
    · rw [hfeq, h1, mul_one]; exact hf1E
    · rw [hfeq, h1]; exact (CFSG.conjugate E N.x).mul_mem hf1E htE
  intro g hg
  have hy : N.x * g * N.x⁻¹ ∈ E := BenderBranch.mem_conjugate_iff.mp hg
  have hgeq : g = N.x⁻¹ * (N.x * g * N.x⁻¹) * N.x := by group
  have hst : s * t * s⁻¹ = t := by rw [C.t_comm hsS]; group
  rcases hE.hEel _ hy with h1 | h1 | h1 | h1
  · have : g = 1 := by rw [hgeq, h1]; group
    rw [this]; simp
  · have : g = t := by rw [hgeq, h1, C.zK_x]
    rw [this, hst]; exact htE
  · have : g = f₁ := by rw [hgeq, h1]
    rw [this]; exact hstar
  · have : g = f₁ * t := by
      rw [hgeq, h1]
      calc N.x⁻¹ * (e * zK) * N.x = (N.x⁻¹ * e * N.x) * (N.x⁻¹ * zK * N.x) := by group
        _ = f₁ * t := by rw [C.zK_x]
    rw [this]
    have e1 : s * (f₁ * t) * s⁻¹ = (s * f₁ * s⁻¹) * (s * t * s⁻¹) := by group
    rw [e1, hst]
    exact (CFSG.conjugate E N.x).mul_mem hstar htE

theorem FinalCtx.normK_conj {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    {n : G} (hnK : n ∈ N.K) (hnE : n ∈ Subgroup.normalizer (E : Set G)) :
    ∀ g ∈ CFSG.conjugate E N.x, n * g * n⁻¹ ∈ E ⊔ CFSG.conjugate E N.x := by
  have heSK : e ∈ N.SK := hE.hEK hE.heE
  have hnH : n ∈ N.H := N.K_le_H hnK
  have hsupL : E ≤ E ⊔ CFSG.conjugate E N.x := le_sup_left
  have hsupR : CFSG.conjugate E N.x ≤ E ⊔ CFSG.conjugate E N.x := le_sup_right
  obtain ⟨hf1mem, hf1sq, hf1ne, hf1zb, hf1E4⟩ := C.refl_image heSK hE.hrefl
  obtain ⟨hf1E, htE⟩ := C.mem_conj_E hE
  set f₁ : G := N.x⁻¹ * e * N.x with hf₁
  have hf₁S : f₁ ∈ N.S := C.SKx_le_S hf1mem
  have hf₁H : f₁ ∈ N.H := N.S_le_H hf₁S
  have hstar : n * f₁ * n⁻¹ ∈ E ⊔ CFSG.conjugate E N.x := by
    have hκK : f₁⁻¹ * n * f₁ * n⁻¹ ∈ N.K := by
      have h1 : f₁⁻¹ * n * f₁ ∈ N.K := by
        have := Subgroup.le_normalizer_iff.mp (N.S_le_normalizer_K C.hKH) f₁⁻¹ (N.S.inv_mem hf₁S)
          n hnK
        simpa using this
      exact N.K.mul_mem h1 (N.K.inv_mem hnK)
    have hκH : f₁⁻¹ * n * f₁ * n⁻¹ ∈ N.H := N.K_le_H hκK
    obtain ⟨ε, hε, hεeq⟩ := klein_comm_mem hE.hrefl hf1E4 (D.K_mem n hnK)
      (C.normKlein_of_normalizes hE hnH hnE)
    have hΦκ : D.Φ (f₁⁻¹ * n * f₁ * n⁻¹) = ε := by
      rw [D.mul _ (N.H.mul_mem (N.H.mul_mem (N.H.inv_mem hf₁H) hnH) hf₁H) _ (N.H.inv_mem hnH),
        D.mul _ (N.H.mul_mem (N.H.inv_mem hf₁H) hnH) _ hf₁H, D.mul _ (N.H.inv_mem hf₁H) _ hnH,
        D.Φ_inv hf₁H, D.Φ_inv hnH]
      calc (D.Φ f₁)⁻¹ * D.Φ n * D.Φ f₁ * (D.Φ n)⁻¹
          = (D.Φ f₁)⁻¹ * (D.Φ n * D.Φ f₁) * (D.Φ n)⁻¹ := by group
        _ = (D.Φ f₁)⁻¹ * (D.Φ f₁ * ε * D.Φ n) * (D.Φ n)⁻¹ := by rw [hεeq]
        _ = ε := by group
    obtain ⟨y, hyE, hyΦ⟩ := C.exists_E_of_klein hE hε
    have hκy : f₁⁻¹ * n * f₁ * n⁻¹ = y :=
      D.inj_K C.hsimple hκK (hE.hEK hyE).2 (by rw [hΦκ, hyΦ])
    have hfeq : n * f₁ * n⁻¹ = f₁ * (f₁⁻¹ * n * f₁ * n⁻¹) := by group
    rw [hfeq, hκy]
    exact (E ⊔ CFSG.conjugate E N.x).mul_mem (hsupR hf1E) (hsupL hyE)
  intro g hg
  have hy : N.x * g * N.x⁻¹ ∈ E := BenderBranch.mem_conjugate_iff.mp hg
  have hgeq : g = N.x⁻¹ * (N.x * g * N.x⁻¹) * N.x := by group
  have hnt : n * t * n⁻¹ = t := by
    have := Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer C.hf.t_mem) n (C.hK0 ▸ hnK)
    rw [this]; group
  rcases hE.hEel _ hy with h1 | h1 | h1 | h1
  · have : g = 1 := by rw [hgeq, h1]; group
    rw [this]; simp
  · have : g = t := by rw [hgeq, h1, C.zK_x]
    rw [this, hnt]; exact hsupR htE
  · have : g = f₁ := by rw [hgeq, h1]
    rw [this]; exact hstar
  · have : g = f₁ * t := by
      rw [hgeq, h1]
      calc N.x⁻¹ * (e * zK) * N.x = (N.x⁻¹ * e * N.x) * (N.x⁻¹ * zK * N.x) := by group
        _ = f₁ * t := by rw [C.zK_x]
    rw [this]
    have e1 : n * (f₁ * t) * n⁻¹ = (n * f₁ * n⁻¹) * (n * t * n⁻¹) := by group
    rw [e1, hnt]
    exact (E ⊔ CFSG.conjugate E N.x).mul_mem hstar (hsupR htE)

theorem FinalCtx.decomp {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    {h : G} (hhH : h ∈ N.H) (hhE : h ∈ Subgroup.normalizer (E : Set G)) :
    ∃ n s, n ∈ N.K ∧ n ∈ Subgroup.normalizer (E : Set G) ∧ s ∈ N.S ∧
      s ∈ Subgroup.normalizer (E : Set G) ∧ h = n * s := by
  have hα : D.Φ h ∈ A6Models.autA6 := D.mem h hhH
  have hn := C.normKlein_of_normalizes hE hhH hhE
  obtain ⟨ψ, π, hψ, hπ, hψn, hπn, hαeq⟩ := norm_decomp hE.hrefl hα hn
  obtain ⟨n, hnK, hnΦ⟩ := D.K_surj ψ hψ
  obtain ⟨s₀, hs₀S, hs₀Φ⟩ := D.S_surj π hπ
  have hnH := N.K_le_H hnK
  have hs₀H := N.S_le_H hs₀S
  have hcH : (n * s₀)⁻¹ * h ∈ N.H := N.H.mul_mem (N.H.inv_mem (N.H.mul_mem hnH hs₀H)) hhH
  have hΦc : D.Φ ((n * s₀)⁻¹ * h) = 1 := by
    rw [D.mul _ (N.H.inv_mem (N.H.mul_mem hnH hs₀H)) _ hhH, D.Φ_inv (N.H.mul_mem hnH hs₀H),
      D.mul n hnH s₀ hs₀H, hnΦ, hs₀Φ, hαeq, inv_mul_cancel]
  have hcC := (D.ker _ hcH).mp hΦc
  have hcS : (n * s₀)⁻¹ * h ∈ N.S := N.mem_S_of_centralizes C.hKH C.h254 C.hZK hcH hcC
  set c := (n * s₀)⁻¹ * h with hcdef
  have hcSC : c ∈ N.SC := D.mem_SC_of_Φ_eq_one C.hK0 hcS hΦc
  have hheq : h = n * (s₀ * c) := by rw [hcdef]; group
  refine ⟨n, s₀ * c, hnK, ?_, N.S.mul_mem hs₀S hcS, ?_, hheq⟩
  · apply mem_normalizer_of_conj_mem
    intro y hy
    have hyK : y ∈ N.K := (hE.hEK hy).2
    have hyH := N.K_le_H hyK
    have hnyK : n * y * n⁻¹ ∈ N.K := (Subgroup.mem_normalizer_iff.mp (C.hKH hnH) y).mp hyK
    obtain ⟨ε', hε', hψε⟩ := hψn _ (C.klein_of_mem_E hE hy)
    obtain ⟨y', hy'E, hy'Φ⟩ := C.exists_E_of_klein hE hε'
    have : n * y * n⁻¹ = y' := D.inj_K C.hsimple hnyK (hE.hEK hy'E).2 (by
      rw [D.Φ_conj hnH hyH, hnΦ, hy'Φ]
      calc ψ * D.Φ y * ψ⁻¹ = (ψ * D.Φ y) * ψ⁻¹ := rfl
        _ = (ε' * ψ) * ψ⁻¹ := by rw [hψε]
        _ = ε' := by group)
    rw [this]; exact hy'E
  · apply mem_normalizer_of_conj_mem
    intro y hy
    have hyK : y ∈ N.K := (hE.hEK hy).2
    have hyH := N.K_le_H hyK
    have hyc : y * c = c * y :=
      Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hcSC) y (C.hK0 ▸ hyK)
    have e1 : s₀ * c * y * (s₀ * c)⁻¹ = s₀ * y * s₀⁻¹ := by
      calc s₀ * c * y * (s₀ * c)⁻¹ = s₀ * (c * y) * c⁻¹ * s₀⁻¹ := by group
        _ = s₀ * (y * c) * c⁻¹ * s₀⁻¹ := by rw [hyc]
        _ = s₀ * y * s₀⁻¹ := by group
    rw [e1]
    have hsyK : s₀ * y * s₀⁻¹ ∈ N.SK :=
      Subgroup.le_normalizer_iff.mp (N.S_le_normalizer_SK C.hKH) s₀ hs₀S y (hE.hEK hy)
    obtain ⟨ε', hε', hπε⟩ := hπn _ (C.klein_of_mem_E hE hy)
    obtain ⟨y', hy'E, hy'Φ⟩ := C.exists_E_of_klein hE hε'
    have : s₀ * y * s₀⁻¹ = y' := D.inj_K C.hsimple hsyK.2 (hE.hEK hy'E).2 (by
      rw [D.Φ_conj hs₀H hyH, hs₀Φ, hy'Φ]
      calc π * D.Φ y * π⁻¹ = (π * D.Φ y) * π⁻¹ := rfl
        _ = (ε' * π) * π⁻¹ := by rw [hπε]
        _ = ε' := by group)
    rw [this]; exact hy'E

theorem FinalCtx.norm_H_le {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e) :
    N.H ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((E ⊔ CFSG.conjugate E N.x : Subgroup G) : Set G) := by
  intro h hh
  obtain ⟨n, s, hnK, hnE, hsS, hsE, rfl⟩ := C.decomp hE hh.1 hh.2
  have hsupL : E ≤ E ⊔ CFSG.conjugate E N.x := le_sup_left
  have hsupR : CFSG.conjugate E N.x ≤ E ⊔ CFSG.conjugate E N.x := le_sup_right
  have hcs : ∀ y ∈ E ⊔ CFSG.conjugate E N.x, s * y * s⁻¹ ∈ E ⊔ CFSG.conjugate E N.x :=
    closed_sup_of (fun y hy => hsupL ((Subgroup.mem_normalizer_iff.mp hsE y).mp hy))
      (fun y hy => hsupR (C.normS_conj hE hsS hsE y hy))
  have hcn : ∀ y ∈ E ⊔ CFSG.conjugate E N.x, n * y * n⁻¹ ∈ E ⊔ CFSG.conjugate E N.x :=
    closed_sup_of (fun y hy => hsupL ((Subgroup.mem_normalizer_iff.mp hnE y).mp hy))
      (fun y hy => C.normK_conj hE hnK hnE y hy)
  apply mem_normalizer_of_conj_mem
  intro y hy
  have h1 := hcn _ (hcs y hy)
  have e1 : n * s * y * (n * s)⁻¹ = n * (s * y * s⁻¹) * n⁻¹ := by group
  rw [e1]
  exact h1

theorem FinalCtx.A_le {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e) :
    E ⊔ CFSG.conjugate E N.x ≤ N.H ⊓ Subgroup.normalizer (E : Set G) := by
  refine sup_le (le_inf (fun y hy => N.S_le_H (N.SK_le_S (hE.hEK hy))) Subgroup.le_normalizer)
    (fun g hg => ?_)
  have hg' : g ∈ CFSG.conjugate N.SK N.x := BenderBranch.conjugate_mono hE.hEK N.x hg
  refine ⟨N.S_le_H (C.SKx_le_S hg'), ?_⟩
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact C.comm_SK_SKx y (hE.hEK hy) g hg'

theorem FinalCtx.z_mem_A {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e) :
    N.z ∈ E ⊔ CFSG.conjugate E N.x := by
  have hsupL : E ≤ E ⊔ CFSG.conjugate E N.x := le_sup_left
  have hsupR : CFSG.conjugate E N.x ≤ E ⊔ CFSG.conjugate E N.x := le_sup_right
  rw [C.hz]
  exact (E ⊔ CFSG.conjugate E N.x).mul_mem (hsupR (C.mem_conj_E hE).2) (hsupL hE.hzKE)

theorem FinalCtx.of_lv (h : Lv2527 N t zK) (D : A6Datum N) : FinalCtx N t zK D := by
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  have hf := h.facts2511
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le hzT, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.S_le_T) hzT.2⟩
  have hΦz : D.Φ N.z = zb := D.Φ_z hK0 h.facts254 hzS
  refine ⟨hK0, hKH, hf, h.facts254, h.facts258, h.concl2525.1, h.concl2525.2,
    (D.Φ_zK hK0 hf).trans hΦz, ?_⟩
  intro i hi hi1 hi2
  by_contra hne
  have htS : t ∈ N.S := N.SC_le_S hf.t_mem
  have hiS : i ∈ N.S := N.SC_le_S hi
  have hc : t * i = i * t := (Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 i hiS).symm
  obtain ⟨E, hEmem, hE4⟩ := exists_four_subgroup hf.t_ne_one hi1 (Ne.symm hne) hf.t_mul_t hi2 hc
  have hEle : E ≤ N.SC := by
    intro y hy
    rcases (hEmem y).1 hy with rfl | rfl | rfl | rfl
    · exact N.SC.one_mem
    · exact hf.t_mem
    · exact hi
    · exact N.SC.mul_mem hf.t_mem hi
  have h2 : 2 ≤ CFSG.Open.pRank 2 N.SC := by
    unfold CFSG.Open.pRank
    exact le_csSup (rankSet_bddAbove N.SC) ⟨E, hEle, hE4.1, by rw [hE4.2]; norm_num⟩
  have h1 : CFSG.Open.pRank 2 N.SC = 1 := h.concl2526
  omega

theorem FinalCtx.exists_E (h : Lv2527 N t zK) (D : A6Datum N) :
    ∃ (E : Subgroup G) (e : G) (C : FinalCtx N t zK D), FinalE C E e ∧ IsFourSubgroup E ∧
      IsUStarPair M N.H (N.S ⊓ Subgroup.normalizer (E : Set G))
        (N.H ⊓ Subgroup.normalizer (E : Set G)) := by
  have C := FinalCtx.of_lv h D
  obtain ⟨E₁, E₂, hE₁K, hE₂K, hE₁4, hE₂4, -, -, -, hstars⟩ := h.concl2523
  have hstar₁ := (hstars E₁ (Set.mem_insert _ _)).1
  obtain ⟨hzKE, e, heE, he1, hezK, hrefl, he2, hEel⟩ :=
    D.four_subgroup_data C.hK0 C.hsimple C.hf C.hΦzK hE₁K hE₁4
  exact ⟨E₁, e, C, ⟨hE₁K, hzKE, heE, hrefl, hEel⟩, hE₁4, hstar₁⟩

end Final

end CFSG.QuasithinUnique
