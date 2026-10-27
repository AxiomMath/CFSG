module

public import CFSG.GH74.GLS.Stage4.RestOut
public import CFSG.GH74.GLS.Stage4.RestSetup
public import CFSG.GH74.GLS.Stage4.HexWeights
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L92

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.DodecA CFSG.GH74.BNPair

variable {G : Type} [Group G]

theorem hinv_inf {H A B : Subgroup G} (hA : HInv H A) (hB : HInv H B) : HInv H (A ⊓ B) :=
  fun h hh _ hx => ⟨hA h hh _ hx.1, hB h hh _ hx.2⟩

theorem hinv_sup {H A B : Subgroup G} (hA : HInv H A) (hB : HInv H B) : HInv H (A ⊔ B) := by
  intro h hh x hx
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj h).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_comap]
      exact mem_sup_left (by simpa [MulAut.conj_apply] using hA h hh y hy)
    · rw [Subgroup.mem_comap]
      exact mem_sup_right (by simpa [MulAut.conj_apply] using hB h hh y hy)
  have := hle hx
  rw [Subgroup.mem_comap] at this
  simpa [MulAut.conj_apply] using this

theorem hinv_bot (H : Subgroup G) : HInv H (⊥ : Subgroup G) := by
  intro h _ x hx
  rw [Subgroup.mem_bot] at hx ⊢
  simp [hx]

@[expose] def Irr (H Y : Subgroup G) : Prop :=
  ∀ V : Subgroup G, V ≤ Y → HInv H V → V = ⊥ ∨ V = Y

theorem Irr.inf {H Y Z : Subgroup G} (hY : Irr H Y) (hYH : HInv H Y) (hZ : HInv H Z) :
    Z ⊓ Y = ⊥ ∨ Z ⊓ Y = Y :=
  hY _ inf_le_right (hinv_inf hZ hYH)

theorem irr_conjBy {H Y : Subgroup G} (hY : Irr H Y) {g : G} (hg : g ∈ normalizer (H : Set G)) :
    Irr H (conjBy g Y) := by
  intro V hVY hV
  have hg' : g⁻¹ ∈ normalizer (H : Set G) := Subgroup.inv_mem _ hg
  have hV' : HInv H (conjBy g⁻¹ V) := HInv.map_conjBy hV hg'
  have hle : conjBy g⁻¹ V ≤ Y := by
    intro x hx
    rw [mem_conjBy_iff] at hx
    have := hVY hx
    rw [mem_conjBy_iff] at this
    have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
    rwa [e] at this
  have hback : conjBy g (conjBy g⁻¹ V) = V := by
    rw [← BNPair.conjBy_mul]
    simp [BNPair.conjBy_one]
  rcases hY _ hle hV' with h | h
  · left
    rw [← hback, h]
    ext x
    simp [mem_conjBy_iff, Subgroup.mem_bot]
  · right
    rw [← hback, h]

theorem eq_sq_sub_sq {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (c : F) :
    ∃ a b : F, c = a ^ 2 - b ^ 2 := by
  refine ⟨(c + 1) / 2, (c - 1) / 2, ?_⟩
  field_simp
  ring

theorem SL2Phi.irred {H : Subgroup G} {r : G} {Ya Yb : Subgroup G} (hP : SL2Phi H r Ya Yb)
    (hodd : Odd (Nat.card ↥Ya)) : Irr H Ya := by
  intro V hVY hV
  obtain ⟨F, hF, hFin, hc, φ, hinj, hU, hL, hD, h, hh, hW⟩ := hP
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    apply Ring.two_ne_zero
    intro hchar
    have h1 := (FiniteField.even_card_iff_char_two).1 hchar
    rw [← Nat.card_eq_fintype_card, hc] at h1
    obtain ⟨k, hk⟩ := hodd
    omega
  by_cases hex : ∃ c₀ : F, c₀ ≠ 0 ∧ φ (sl2U c₀) ∈ V
  · right
    obtain ⟨c₀, hc₀, hcV⟩ := hex
    have hsq : ∀ t : F, φ (sl2U (t ^ 2 * c₀)) ∈ V := by
      intro t
      by_cases ht : t = 0
      · simp [ht, sl2U_zero]
      · let u : Fˣ := Units.mk0 t ht
        have hconj := hV (φ (sl2D u)) (hD u) _ hcV
        have e : φ (sl2D u) * φ (sl2U c₀) * (φ (sl2D u))⁻¹ = φ (sl2U (t ^ 2 * c₀)) := by
          rw [← map_mul, ← map_inv, ← map_mul]
          congr 1
          rw [sl2D_mul_sl2U]
          simp [u]
        rwa [e] at hconj
    have hall : ∀ x : F, φ (sl2U x) ∈ V := by
      intro x
      obtain ⟨a, b, hab⟩ := eq_sq_sub_sq h2 (x / c₀)
      have e : x = a ^ 2 * c₀ + (-(b ^ 2 * c₀)) := by
        field_simp at hab ⊢
        linear_combination hab
      rw [e, sl2U_add, map_mul]
      refine V.mul_mem (hsq a) ?_
      have : φ (sl2U (-(b ^ 2 * c₀))) = (φ (sl2U (b ^ 2 * c₀)))⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← map_mul, ← sl2U_add]
        simp [sl2U_zero]
      rw [this]
      exact V.inv_mem (hsq b)
    refine le_antisymm hVY (fun y hy => ?_)
    obtain ⟨c, rfl⟩ := (hU y).1 hy
    exact hall c
  · left
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨c, rfl⟩ := (hU v).1 (hVY hv)
    by_cases hc0 : c = 0
    · simp [hc0, sl2U_zero]
    · exact absurd ⟨c, hc0, hv⟩ hex

@[expose] def projSub (A B M : Subgroup G) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Subgroup G where
  carrier := {a | a ∈ A ∧ ∃ b ∈ B, a * b ∈ M}
  one_mem' := ⟨A.one_mem, 1, B.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, b, hb, hxb⟩ ⟨hy, b', hb', hyb'⟩
    refine ⟨A.mul_mem hx hy, b * b', B.mul_mem hb hb', ?_⟩
    have e : x * y * (b * b') = (x * b) * (y * b') := by
      calc x * y * (b * b') = x * (y * b) * b' := by group
        _ = x * (b * y) * b' := by rw [hcomm y hy b hb]
        _ = (x * b) * (y * b') := by group
    rw [e]
    exact M.mul_mem hxb hyb'
  inv_mem' := by
    rintro x ⟨hx, b, hb, hxb⟩
    refine ⟨A.inv_mem hx, b⁻¹, B.inv_mem hb, ?_⟩
    have e : x⁻¹ * b⁻¹ = (x * b)⁻¹ := by
      calc x⁻¹ * b⁻¹ = (b * x)⁻¹ := by group
        _ = (x * b)⁻¹ := by rw [hcomm x hx b hb]
    rw [e]
    exact M.inv_mem hxb

theorem projSub_le {A B M : Subgroup G} {hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} :
    projSub A B M hcomm ≤ A := fun _ hx => hx.1

theorem hinv_projSub {H A B M : Subgroup G} {hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a}
    (hAH : HInv H A) (hBH : HInv H B) (hM : HInv H M) : HInv H (projSub A B M hcomm) := by
  rintro h hh x ⟨hx, b, hb, hxb⟩
  refine ⟨hAH h hh x hx, h * b * h⁻¹, hBH h hh b hb, ?_⟩
  have e : h * x * h⁻¹ * (h * b * h⁻¹) = h * (x * b) * h⁻¹ := by group
  rw [e]
  exact hM h hh _ hxb

theorem hinv_sup_two {H A B M : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAH : HInv H A) (hBH : HInv H B) (hAirr : Irr H A) (hBirr : Irr H B) (hne : ¬ HEquiv H A B)
    (hMle : M ≤ A ⊔ B) (hM : HInv H M) :
    (∀ m ∈ M, ∃ a ∈ M ⊓ A, ∃ b ∈ M ⊓ B, m = a * b) ∧
      (M ⊓ A = ⊥ ∨ M ⊓ A = A) ∧ (M ⊓ B = ⊥ ∨ M ⊓ B = B) := by
  have hMA := hAirr.inf hAH hM
  have hMB := hBirr.inf hBH hM
  refine ⟨?_, hMA, hMB⟩
  intro m hm
  obtain ⟨a₀, ha₀, b₀, hb₀, hm'⟩ := (mem_sup_iff_of_comm hcomm m).1 (hMle hm)
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  set PA := projSub A B M hcomm with hPAdef
  set PB := projSub B A M hcomm' with hPBdef
  have hPAirr := hAirr PA projSub_le (hinv_projSub hAH hBH hM)
  have hPBirr := hBirr PB projSub_le (hinv_projSub hBH hAH hM)
  have ha₀P : a₀ ∈ PA := ⟨ha₀, b₀, hb₀, hm' ▸ hm⟩
  have hb₀P : b₀ ∈ PB := ⟨hb₀, a₀, ha₀, by rw [hcomm' b₀ hb₀ a₀ ha₀]; exact hm' ▸ hm⟩
  by_cases hPA : PA = ⊥
  · rw [hPA, Subgroup.mem_bot] at ha₀P
    refine ⟨1, ⟨M.one_mem, A.one_mem⟩, m, ⟨hm, ?_⟩, by simp⟩
    rw [hm', ha₀P, one_mul]
    exact hb₀
  by_cases hPB : PB = ⊥
  · rw [hPB, Subgroup.mem_bot] at hb₀P
    refine ⟨m, ⟨hm, ?_⟩, 1, ⟨M.one_mem, B.one_mem⟩, by simp⟩
    rw [hm', hb₀P, mul_one]
    exact ha₀
  have hPA' : PA = A := hPAirr.resolve_left hPA
  have hPB' : PB = B := hPBirr.resolve_left hPB
  rcases hMA with hMA0 | hMA1
  · rcases hMB with hMB0 | hMB1
    ·
      exfalso
      apply hne
      have huniq : ∀ a ∈ A, ∀ b ∈ B, ∀ b' ∈ B, a * b ∈ M → a * b' ∈ M → b = b' := by
        intro a ha b hb b' hb' hab hab'
        have h1 : b⁻¹ * b' ∈ M := by
          have e : b⁻¹ * b' = (a * b)⁻¹ * (a * b') := by group
          rw [e]
          exact M.mul_mem (M.inv_mem hab) hab'
        have h2 : b⁻¹ * b' ∈ M ⊓ B := ⟨h1, B.mul_mem (B.inv_mem hb) hb'⟩
        rw [hMB0, Subgroup.mem_bot] at h2
        exact inv_mul_eq_one.1 h2
      have hexA : ∀ a ∈ A, ∃ b ∈ B, a * b ∈ M := by
        intro a ha
        have : a ∈ PA := by rw [hPA']; exact ha
        exact this.2
      choose! f hfB hfM using hexA
      have hf1 : f 1 = 1 := huniq 1 A.one_mem _ (hfB 1 A.one_mem) 1 B.one_mem (hfM 1 A.one_mem)
        (by simp)
      have hfmul : ∀ a ∈ A, ∀ a' ∈ A, f (a * a') = f a * f a' := by
        intro a ha a' ha'
        refine huniq (a * a') (A.mul_mem ha ha') _ (hfB _ (A.mul_mem ha ha')) _
          (B.mul_mem (hfB a ha) (hfB a' ha')) (hfM _ (A.mul_mem ha ha')) ?_
        have e : a * a' * (f a * f a') = (a * f a) * (a' * f a') := by
          calc a * a' * (f a * f a') = a * (a' * f a) * f a' := by group
            _ = a * (f a * a') * f a' := by rw [hcomm a' ha' (f a) (hfB a ha)]
            _ = (a * f a) * (a' * f a') := by group
        rw [e]
        exact M.mul_mem (hfM a ha) (hfM a' ha')
      let φ : ↥A →* ↥B :=
        { toFun := fun a => ⟨f a, hfB a a.2⟩
          map_one' := Subtype.ext hf1
          map_mul' := fun a a' => Subtype.ext (hfmul a a.2 a' a'.2) }
      have hφinj : Function.Injective φ := by
        intro a a' haa
        have hfa : f a = f a' := congrArg Subtype.val haa
        have h1 : (a : G) * (a' : G)⁻¹ ∈ M := by
          have e : (a : G) * (a' : G)⁻¹ = ((a : G) * f a) * ((a' : G) * f a')⁻¹ := by
            rw [hfa]
            group
          rw [e]
          exact M.mul_mem (hfM a a.2) (M.inv_mem (hfM a' a'.2))
        have h2 : (a : G) * (a' : G)⁻¹ ∈ M ⊓ A := ⟨h1, A.mul_mem a.2 (A.inv_mem a'.2)⟩
        rw [hMA0, Subgroup.mem_bot] at h2
        exact Subtype.ext (mul_inv_eq_one.1 h2)
      have hφsurj : Function.Surjective φ := by
        rintro ⟨b, hb⟩
        have hbP : b ∈ PB := by rw [hPB']; exact hb
        obtain ⟨-, a, ha, hba⟩ := hbP
        refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
        have hab : a * b ∈ M := by rw [hcomm a ha b hb]; exact hba
        exact huniq a ha _ (hfB a ha) b hb (hfM a ha) hab
      refine ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩, ?_⟩
      intro h hh x hx
      show f (h * (x : G) * h⁻¹) = h * f x * h⁻¹
      refine huniq _ hx _ (hfB _ hx) _ (hBH h hh _ (hfB x x.2)) (hfM _ hx) ?_
      have e : h * (x : G) * h⁻¹ * (h * f x * h⁻¹) = h * ((x : G) * f x) * h⁻¹ := by group
      rw [e]
      exact hM h hh _ (hfM x x.2)
    ·
      have hBM : B ≤ M := hMB1.symm.le.trans inf_le_left
      refine ⟨a₀, ⟨?_, ha₀⟩, b₀, ⟨hBM hb₀, hb₀⟩, hm'⟩
      have : a₀ = m * b₀⁻¹ := by rw [hm']; group
      rw [this]
      exact M.mul_mem hm (M.inv_mem (hBM hb₀))
  ·
    have hAM : A ≤ M := hMA1.symm.le.trans inf_le_left
    refine ⟨a₀, ⟨hAM ha₀, ha₀⟩, b₀, ⟨?_, hb₀⟩, hm'⟩
    have : b₀ = a₀⁻¹ * m := by rw [hm']; group
    rw [this]
    exact M.mul_mem (M.inv_mem (hAM ha₀)) hm

end CFSG.GH74.GLS.Stage4.Rest.L92
