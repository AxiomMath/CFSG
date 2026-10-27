module

public import CFSG.CGT.PushingUpLit.A78Sp4.Chain
public import CFSG.CGT.PushingUpLit.A78Sp4.CentralU
public import CFSG.CGT.PushingUpLit.A78Sp4.Z1
public import CFSG.CGT.PushingUpLit.A78Sp4.CL
public import CFSG.CGT.PushingUpLit.A78Sp4.Prop2Loc

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_cj {g : G} {H : Subgroup G} (h : cj g H = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← mul_mem_cj_iff g H x, h]

variable {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem Sp4Base.mem_normalizer_J (h : Sp4Base G V V₂ J T S M M₂ e) {s : G} (hs : s ∈ S) :
    s ∈ Subgroup.normalizer (J : Set G) :=
  mem_normalizer_of_cj (cj_eq_of_normalizes (fun _ hx => h.conj_J hs hx) fun x hx => by
    simpa using h.conj_J (S.inv_mem hs) hx)

theorem Sp4Base.V_ne (h : Sp4Base G V V₂ J T S M M₂ e) : V ≠ V₂ := by
  intro hVV
  have h1 := h.card_inf
  rw [hVV, inf_idem, h.card_V₂] at h1
  have h2 := Nat.pow_right_injective (le_refl 2) h1
  have := h.two_le
  omega

theorem Sp4Loc.mem_normalizer_of_mem_M [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e)
    {u : G} (hu : UType V V₂ Z Z₂ u) {m : G} (hm : m ∈ M)
    (hmu : m ∈ Subgroup.centralizer ({u} : Set G)) : m ∈ Subgroup.normalizer (J : Set G) := by
  have hJ := h.cross.cent_L u hu.1 hu.2.1
  have key : ∀ k ∈ M, k ∈ Subgroup.centralizer ({u} : Set G) → ∀ x ∈ J, k * x * k⁻¹ ∈ J := by
    intro k hk hku x hx
    rw [← hJ] at hx ⊢
    exact ⟨h.side₁.conj_mem_L hk hx.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hku hx.2) (Subgroup.inv_mem _ hku)⟩
  exact mem_normalizer_of_cj (cj_eq_of_normalizes (key m hm hmu) fun x hx => by
    simpa using key m⁻¹ (M.inv_mem hm) (Subgroup.inv_mem _ hmu) x hx)

theorem Sp4Loc.stmt410_of_central [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e)
    (hc : ∀ u, UType V V₂ Z Z₂ u → (∀ s ∈ S, s * u = u * s) →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)) :
    Sp4Stmt410 V V₂ Z Z₂ J := by
  intro u hu x hx
  obtain ⟨u₀, hu₀, hcen⟩ := exists_central_uType h
  obtain ⟨n, hn, rfl⟩ := h.cross.u_conj u₀ u hu₀ hu
  rw [← cj_centralizer_singleton, mem_cj_iff] at hx
  have h1 := hc u₀ hu₀ hcen hx
  have e1 : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn h1) (Subgroup.inv_mem _ hn)

theorem Sp4Loc.normalizer_of_le [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e)
    {u : G} (hu : UType V V₂ Z Z₂ u) (hcen : ∀ s ∈ S, s * u = u * s) {Q : Subgroup G}
    (hQS : Q ≤ S) (hQn : ∀ c ∈ Subgroup.centralizer ({u} : Set G), ∀ x ∈ Q, c * x * c⁻¹ ∈ Q)
    (hZJ : V ⊓ V₂ ≤ Q) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  set C := Subgroup.centralizer ({u} : Set G) with hC
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hcen s hs)
  have hcjQ : ∀ c ∈ C, cj c Q ≤ Q := fun c hc x hx => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact hQn c hc y hy
  have hVJ : V ≤ J := by rw [← h.base.sup]; exact le_sup_left
  have hV₂J : V₂ ≤ J := by rw [← h.base.sup]; exact le_sup_right
  have hZV : Z ≤ V := by rw [h.side₁.Z_eq]; exact inf_le_left
  have hZQ : Z ≤ Q := fun x hx => hZJ ⟨hZV hx, h.cross.Z_le hx⟩
  obtain ⟨s₀, hs₀S, hs₀T⟩ := h.base.exists_swap
  have hs₀C : s₀ ∈ C := hSC hs₀S
  have hsw := h.base.swap s₀ hs₀S hs₀T
  by_cases hJQ : J ≤ Q
  ·
    intro c hc
    have hcV : ∀ U : Subgroup G, ElemAb2 U → Nat.card U = 2 ^ (3 * e) → U ≤ Q →
        cj c U = V ∨ cj c U = V₂ := fun U hU hUc hUQ =>
      h.base.A_S _ (((cj_mono c hUQ).trans (hcjQ c hc)).trans hQS) (elemAb2_cj hU c)
        ((card_cj c U).trans hUc)
    have h1 := hcV V h.base.elem_V h.base.card_V (hVJ.trans hJQ)
    have h2 := hcV V₂ h.base.elem_V₂ h.base.card_V₂ (hV₂J.trans hJQ)
    have hne : cj c V ≠ cj c V₂ := fun heq =>
      h.base.V_ne (Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective heq)
    have hJ : cj c J = J := by
      rw [← h.base.sup, cj_sup_eq]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2]
      · rw [h1, h2, sup_comm]
      · exact absurd (h1.trans h2.symm) hne
    exact mem_normalizer_of_cj hJ
  ·
    have hconj : ∀ c ∈ C, cj c Z = Z ∨ cj c Z = Z₂ := by
      intro c hc
      have hcQ : cj c Z ≤ Q := (cj_mono c hZQ).trans (hcjQ c hc)
      rcases sp4_prop2 h c (hcQ.trans hQS) with hV' | hV₂'
      · rcases h.cross.conj_in_V _ ⟨c, Or.inl rfl⟩ hV' with h1 | ⟨h1, -⟩
        · exact h1
        · exfalso
          apply hJQ
          have hVQ : V ≤ Q := by rw [← h1]; exact sup_le hZJ hcQ
          have hV₂Q : V₂ ≤ Q := by
            rw [← hsw.1]; exact (cj_mono s₀ hVQ).trans (hcjQ s₀ hs₀C)
          rw [← h.base.sup]
          exact sup_le hVQ hV₂Q
      · rcases h.cross.conj_in_V₂ _ ⟨c, Or.inl rfl⟩ hV₂' with h1 | ⟨h1, -⟩
        · exact h1
        · exfalso
          apply hJQ
          have hV₂Q : V₂ ≤ Q := by rw [← h1]; exact sup_le hZJ hcQ
          have hVQ : V ≤ Q := by
            rw [← hsw.2]; exact (cj_mono s₀ hV₂Q).trans (hcjQ s₀ hs₀C)
          rw [← h.base.sup]
          exact sup_le hVQ hV₂Q
    have hM : ∀ m ∈ C, cj m Z = Z → m ∈ Subgroup.normalizer (J : Set G) := fun m hm hmZ =>
      h.mem_normalizer_of_mem_M hu (by rw [← h.side₁.normalizer_Z]; exact mem_normalizer_of_cj hmZ)
        hm
    intro c hc
    rcases hconj c hc with h1 | h1
    · exact hM c hc h1
    · have h2 : cj (s₀ * c) Z = Z := by
        rw [← cj_cj, h1, (h.cross.swap_Z s₀ hs₀S hs₀T).2]
      have h3 := hM _ (C.mul_mem hs₀C hc) h2
      have e1 : c = s₀⁻¹ * (s₀ * c) := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (h.base.mem_normalizer_J hs₀S)) h3

theorem Sp4Loc.four_lt_commSet [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e)
    (he : 3 ≤ e) {c : Cls2Coord (GaloisField 2 e) J} (hV : ∀ x ∈ J, (x ∈ V ↔ (c.π x).2 = 0))
    (hV₂ : ∀ x ∈ J, (x ∈ V₂ ↔ (c.π x).1 = 0)) {s : G} (hs : s ∈ S) (hsJ : s ∉ J) :
    4 < (commSet c s).ncard := by
  have hsn : ∀ x ∈ J, s * x * s⁻¹ ∈ J := fun x hx => h.base.conj_J hs hx
  have hsn' : ∀ x ∈ J, s⁻¹ * x * s⁻¹⁻¹ ∈ J := fun x hx => h.base.conj_J (S.inv_mem hs) hx
  have hsn'' : ∀ x ∈ J, s⁻¹ * x * s ∈ J := fun x hx => by simpa using hsn' x hx
  have hsn''' : ∀ x ∈ J, s⁻¹⁻¹ * x * s⁻¹ ∈ J := fun x hx => by simpa using hsn x hx
  obtain ⟨gb, Γ, hA⟩ := c.exists_actsAs hsn hsn''
  obtain ⟨gb', Γ', hA'⟩ := c.exists_actsAs hsn' hsn'''
  have hbij := hA.bijective hA' hsn hsn''
  have hcomp := hA.hcomp hsn
  have hq : 8 ≤ Nat.card (GaloisField 2 e) := by
    rw [GaloisField.card 2 e (by omega)]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hform : IsDiagForm gb ∨ IsSwapForm gb := by
    by_cases hT : s ∈ T
    · exact Or.inl (cl_diag_W hq hcomp (hA.axes_diag (h.base.wdiag c hV hV₂ hT)) hbij)
    · exact Or.inr (cl_swap_W hq hcomp (hA.axes_swap (h.base.wswap c hV hV₂ hs hT)) hbij)
  have hne : gb ≠ AddMonoidHom.id _ := by
    intro hid
    obtain ⟨y, hy, hy0⟩ := h.base.faithful c hV hV₂ hs hsJ
    have hmem : c.π ⁅s, y⁆ ∈ commSet c s := ⟨y, hy, rfl⟩
    rw [hA.commSet_eq_range hsn, hid] at hmem
    obtain ⟨w, hw⟩ := hmem
    apply hy0
    rw [← hw]
    exact Prod.ext (CharTwo.add_self_eq_zero w.1) (CharTwo.add_self_eq_zero w.2)
  rw [hA.commSet_eq_range hsn]
  exact card_image_ge hq hform hne

theorem sp4_410_ge3 [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (he : 3 ≤ e) :
    Sp4Stmt410 V V₂ Z Z₂ J := by
  refine h.stmt410_of_central fun u hu hcen => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({u} : Set G) with hC
  set Q := CFSG.Open.pCoreOf 2 C with hQ
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hcen s hs)
  have hQS : Q ≤ S := pCoreOf_le_of_isSylowOf (h.base.sylow.of_le hSC le_top)
  have hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc q hq =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hc) q).1 hq
  have hu2 : u * u = 1 := (h.base.elem_V u hu.1.1 u hu.1.1).2
  have hu1 : u ≠ 1 := fun h1 => hu.2.1 (h1 ▸ Z.one_mem)
  have hVJ : V ≤ J := by rw [← h.base.sup]; exact le_sup_left
  obtain ⟨c, hV, hV₂, -, -⟩ := exists_cls2 h.coords
  have hz := z1 c h.base.J_le_S (fun s hs x hx => h.base.conj_J hs hx)
    (fun s hs hsJ => h.four_lt_commSet he hV hV₂ hs hsJ) hQS (fun s hs x hx => hQn s (hSC hs) x hx)
    (fun s hs hsQ => cent_le_pCoreOf h.charTwo hu2 hu1
      ⟨hSC hs, Subgroup.mem_centralizer_iff.2 fun x hx => (hsQ x hx).symm⟩)
  refine h.normalizer_of_le hu hcen hQS hQn fun x hx => hz x (hVJ hx.1) ?_
  have hxJ := hVJ hx.1
  exact Prod.ext ((hV₂ x hxJ).1 hx.2) ((hV x hxJ).1 hx.1)

theorem sp4Chain410GE3 : Sp4Chain410GE3 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hloc he => sp4_410_ge3 hloc he

end CFSG.CGT.PushingUpLit.A78Sp4
