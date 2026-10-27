module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {X G₀ : Type*} [Group X] [Group G₀]

theorem exists_mul_eq_of_sup_eq {H L C : Subgroup X} (hCH : C ≤ H) (hHLC : L ⊔ C = H)
    (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) {h : X} (hh : h ∈ H) :
    ∃ l ∈ L, ∃ c ∈ C, h = l * c := by
  let S : Subgroup X :=
    { carrier := {x | ∃ l ∈ L, ∃ c ∈ C, x = l * c}
      one_mem' := ⟨1, L.one_mem, 1, C.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, c₁, hc₁, rfl⟩ ⟨l₂, hl₂, c₂, hc₂, rfl⟩
        exact ⟨l₁ * (c₁ * l₂ * c₁⁻¹), L.mul_mem hl₁ (hLn c₁ (hCH hc₁) l₂ hl₂), c₁ * c₂,
          C.mul_mem hc₁ hc₂, by group⟩
      inv_mem' := by
        rintro _ ⟨l, hl, c, hc, rfl⟩
        refine ⟨c⁻¹ * l⁻¹ * c, ?_, c⁻¹, C.inv_mem hc, by group⟩
        simpa using hLn c⁻¹ (hCH (C.inv_mem hc)) l⁻¹ (L.inv_mem hl) }
  have hS : L ⊔ C ≤ S :=
    sup_le (fun l hl => ⟨l, hl, 1, C.one_mem, (mul_one l).symm⟩)
      (fun c hc => ⟨1, L.one_mem, c, hc, (one_mul c).symm⟩)
  exact hS (hHLC ▸ hh)

private theorem mem_iff_conj_mem {K : Type*} [Group K] {H L : Subgroup K}
    (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) {g : K} (hg : g ∈ H) (s : K) :
    s ∈ L ↔ g * s * g⁻¹ ∈ L :=
  ⟨hLn g hg s, fun hs => by simpa [mul_assoc] using hLn g⁻¹ (H.inv_mem hg) _ hs⟩

private def conjAut {K : Type*} [Group K] (S : Subgroup K) (g : K)
    (hg : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S) : ↥S ≃* ↥S where
  toFun s := ⟨g * s * g⁻¹, (hg s).1 s.2⟩
  invFun s := ⟨g⁻¹ * s * g, (hg (g⁻¹ * s * g)).2 (by
    have h : g * (g⁻¹ * (s : K) * g) * g⁻¹ = s := by group
    rw [h]
    exact s.2)⟩
  left_inv s := by ext; simp [mul_assoc]
  right_inv s := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem exists_hom_of_sup_eq {H L C : Subgroup X} {H₀ L₀ : Subgroup G₀}
    (hLH : L ≤ H) (hCH : C ≤ H) (hHLC : L ⊔ C = H) (hLn : (L.subgroupOf H).Normal)
    (hL₀H₀ : L₀ ≤ H₀) (hL₀n : (L₀.subgroupOf H₀).Normal)
    (ψL : ↥L ≃* ↥L₀) (ψC : ↥C →* ↥H₀)
    (hagree : ∀ (x : X) (hxL : x ∈ L) (hxC : x ∈ C),
      Subgroup.inclusion hL₀H₀ (ψL ⟨x, hxL⟩) = ψC ⟨x, hxC⟩)
    (hrigid : ∀ α : ↥L₀ ≃* ↥L₀,
      (∀ (b : X) (hbL : b ∈ L), b ∈ C → α (ψL ⟨b, hbL⟩) = ψL ⟨b, hbL⟩) → α = MulEquiv.refl _) :
    ∃ ψH : ↥H →* ↥H₀,
      (∀ l : ↥L, ψH (Subgroup.inclusion hLH l) = Subgroup.inclusion hL₀H₀ (ψL l)) ∧
      (∀ c : ↥C, ψH (Subgroup.inclusion hCH c) = ψC c) := by
  have hLn' : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := fun h hh l hl =>
    (Subgroup.normal_subgroupOf_iff hLH).1 hLn l h hl hh
  have hL₀n' : ∀ h ∈ H₀, ∀ l ∈ L₀, h * l * h⁻¹ ∈ L₀ := fun h hh l hl =>
    (Subgroup.normal_subgroupOf_iff hL₀H₀).1 hL₀n l h hl hh
  have hagreeG : ∀ (x : X) (hxL : x ∈ L) (hxC : x ∈ C),
      ((ψL ⟨x, hxL⟩ : ↥L₀) : G₀) = ((ψC ⟨x, hxC⟩ : ↥H₀) : G₀) := fun x hxL hxC => by
    have := congrArg Subtype.val (hagree x hxL hxC)
    simpa using this
  let σ : ↥C → (↥L ≃* ↥L) := fun c =>
    conjAut L (c : X) (mem_iff_conj_mem hLn' (hCH c.2))
  let τ : ↥C → (↥L₀ ≃* ↥L₀) := fun c =>
    conjAut L₀ ((ψC c : ↥H₀) : G₀) (mem_iff_conj_mem hL₀n' (ψC c).2)
  have hσ : ∀ (c : ↥C) (l : ↥L), (ψL.symm.trans ((σ c).trans ψL)) (ψL l) =
      ψL ⟨c * l * c⁻¹, hLn' c (hCH c.2) l l.2⟩ := fun c l => by
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
    rfl
  have hτ : ∀ (c : ↥C) (l : ↥L), (((τ c) (ψL l) : ↥L₀) : G₀) =
      (ψC c : G₀) * (ψL l : G₀) * (ψC c : G₀)⁻¹ := fun c l => rfl
  have hconj : ∀ c : ↥C, ψL.symm.trans ((σ c).trans ψL) = τ c := by
    intro c
    have h1 := hrigid ((ψL.symm.trans ((σ c).trans ψL)).trans (τ c).symm) (by
      intro b hbL hbC
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq, hσ c ⟨b, hbL⟩]
      apply Subtype.ext
      have hcb : (c : X) * b * (c : X)⁻¹ ∈ C := C.mul_mem (C.mul_mem c.2 hbC) (C.inv_mem c.2)
      have e1 := hagreeG (c * b * c⁻¹) (hLn' c (hCH c.2) b hbL) hcb
      have e2 := hagreeG b hbL hbC
      rw [hτ c ⟨b, hbL⟩]
      change ((ψL ⟨c * b * c⁻¹, _⟩ : ↥L₀) : G₀) = _
      rw [e1, e2]
      have : (⟨c * b * c⁻¹, hcb⟩ : ↥C) = c * ⟨b, hbC⟩ * c⁻¹ := rfl
      rw [this]
      simp)
    refine MulEquiv.ext fun x => ?_
    have hx := DFunLike.congr_fun h1 x
    rw [MulEquiv.trans_apply, MulEquiv.refl_apply] at hx
    exact (τ c).symm_apply_eq.1 hx
  have hkeyG : ∀ (c : ↥C) (l : ↥L),
      ((ψL ⟨c * l * c⁻¹, hLn' c (hCH c.2) l l.2⟩ : ↥L₀) : G₀) =
        (ψC c : G₀) * (ψL l : G₀) * (ψC c : G₀)⁻¹ := fun c l => by
    rw [← hτ c l, ← hσ c l, hconj c]
  have hkey : ∀ (c : ↥C) (l : ↥L),
      Subgroup.inclusion hL₀H₀ (ψL ⟨c * l * c⁻¹, hLn' c (hCH c.2) l l.2⟩) =
        ψC c * Subgroup.inclusion hL₀H₀ (ψL l) * (ψC c)⁻¹ := fun c l =>
    Subtype.ext (by simpa using hkeyG c l)
  have hagree' : ∀ (a : ↥L) (b : ↥C), (a : X) = b →
      Subgroup.inclusion hL₀H₀ (ψL a) = ψC b := fun a b hab => by
    have h := hagree a a.2 (hab ▸ b.2)
    have hb : (⟨(a : X), hab ▸ b.2⟩ : ↥C) = b := Subtype.ext hab
    rw [hb] at h
    exact h
  have hwell : ∀ (l₁ l₂ : ↥L) (c₁ c₂ : ↥C), (l₁ : X) * c₁ = l₂ * c₂ →
      Subgroup.inclusion hL₀H₀ (ψL l₁) * ψC c₁ = Subgroup.inclusion hL₀H₀ (ψL l₂) * ψC c₂ := by
    intro l₁ l₂ c₁ c₂ h
    have hx : ((l₂⁻¹ * l₁ : ↥L) : X) = ((c₂ * c₁⁻¹ : ↥C) : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (l₂ : X)⁻¹ * l₁ = (l₂ : X)⁻¹ * (l₁ * c₁) * (c₁ : X)⁻¹ := by group
        _ = (l₂ : X)⁻¹ * (l₂ * c₂) * (c₁ : X)⁻¹ := by rw [h]
        _ = c₂ * (c₁ : X)⁻¹ := by group
    have h2 := hagree' (l₂⁻¹ * l₁) (c₂ * c₁⁻¹) hx
    simp only [map_mul, map_inv] at h2
    have h3 : Subgroup.inclusion hL₀H₀ (ψL l₁) =
        Subgroup.inclusion hL₀H₀ (ψL l₂) * (ψC c₂ * (ψC c₁)⁻¹) := by
      rw [← h2]; group
    rw [h3]
    group
  have hdec : ∀ h : ↥H, ∃ (l : ↥L) (c : ↥C), (h : X) = l * c := fun h => by
    obtain ⟨l, hl, c, hc, hlc⟩ := exists_mul_eq_of_sup_eq hCH hHLC hLn' h.2
    exact ⟨⟨l, hl⟩, ⟨c, hc⟩, hlc⟩
  choose l c hlc using hdec
  let f : ↥H → ↥H₀ := fun h => Subgroup.inclusion hL₀H₀ (ψL (l h)) * ψC (c h)
  have hf : ∀ (h : ↥H) (l' : ↥L) (c' : ↥C), (h : X) = l' * c' →
      f h = Subgroup.inclusion hL₀H₀ (ψL l') * ψC c' := fun h l' c' hh =>
    hwell _ _ _ _ ((hlc h).symm.trans hh)
  have hmul : ∀ h₁ h₂ : ↥H, f (h₁ * h₂) = f h₁ * f h₂ := by
    intro h₁ h₂
    let l₂' : ↥L := ⟨(c h₁ : X) * l h₂ * (c h₁ : X)⁻¹, hLn' _ (hCH (c h₁).2) _ (l h₂).2⟩
    have hdecomp : ((h₁ * h₂ : ↥H) : X) = ((l h₁ * l₂' : ↥L) : X) * ((c h₁ * c h₂ : ↥C) : X) := by
      simp only [Subgroup.coe_mul, l₂']
      rw [hlc h₁, hlc h₂]
      group
    rw [hf (h₁ * h₂) (l h₁ * l₂') (c h₁ * c h₂) hdecomp]
    have e : Subgroup.inclusion hL₀H₀ (ψL l₂') = ψC (c h₁) *
        Subgroup.inclusion hL₀H₀ (ψL (l h₂)) * (ψC (c h₁))⁻¹ := hkey (c h₁) (l h₂)
    calc Subgroup.inclusion hL₀H₀ (ψL (l h₁ * l₂')) * ψC (c h₁ * c h₂)
        = Subgroup.inclusion hL₀H₀ (ψL (l h₁)) * Subgroup.inclusion hL₀H₀ (ψL l₂') *
            (ψC (c h₁) * ψC (c h₂)) := by simp only [map_mul]
      _ = Subgroup.inclusion hL₀H₀ (ψL (l h₁)) * (ψC (c h₁) *
            Subgroup.inclusion hL₀H₀ (ψL (l h₂)) * (ψC (c h₁))⁻¹) *
            (ψC (c h₁) * ψC (c h₂)) := by rw [e]
      _ = f h₁ * f h₂ := by simp only [f]; group
  refine ⟨MonoidHom.mk' f hmul, fun l₀ => ?_, fun c₀ => ?_⟩
  · show f (Subgroup.inclusion hLH l₀) = _
    rw [hf (Subgroup.inclusion hLH l₀) l₀ 1 (by simp)]
    simp
  · show f (Subgroup.inclusion hCH c₀) = _
    rw [hf (Subgroup.inclusion hCH c₀) 1 c₀ (by simp)]
    simp

theorem injective_of_restrict {H L C : Subgroup X} {H₀ L₀ : Subgroup G₀}
    (hLH : L ≤ H) (hCH : C ≤ H) (hHLC : L ⊔ C = H) (hLn : (L.subgroupOf H).Normal)
    (hL₀H₀ : L₀ ≤ H₀) (ψL : ↥L ≃* ↥L₀) (ψC : ↥C →* ↥H₀) (ψH : ↥H →* ↥H₀)
    (hψL : ∀ l : ↥L, ψH (Subgroup.inclusion hLH l) = Subgroup.inclusion hL₀H₀ (ψL l))
    (hψC : ∀ c : ↥C, ψH (Subgroup.inclusion hCH c) = ψC c)
    (hψCL : ∀ c : ↥C, ((ψC c : ↥H₀) : G₀) ∈ L₀ → (c : X) ∈ L) :
    Function.Injective ψH := by
  have hLn' : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := fun h hh l hl =>
    (Subgroup.normal_subgroupOf_iff hLH).1 hLn l h hl hh
  rw [injective_iff_map_eq_one]
  intro h hh
  obtain ⟨l, hl, c, hc, hlc⟩ := exists_mul_eq_of_sup_eq hCH hHLC hLn' h.2
  have hh' : h = Subgroup.inclusion hLH ⟨l, hl⟩ * Subgroup.inclusion hCH ⟨c, hc⟩ :=
    Subtype.ext hlc
  rw [hh', map_mul, hψL, hψC] at hh
  have hψc : ψC ⟨c, hc⟩ = (Subgroup.inclusion hL₀H₀ (ψL ⟨l, hl⟩))⁻¹ :=
    eq_inv_of_mul_eq_one_right hh
  have hcL : c ∈ L := hψCL ⟨c, hc⟩ (by
    rw [hψc]
    simpa using L₀.inv_mem (ψL ⟨l, hl⟩).2)
  have h2 : ψH (Subgroup.inclusion hLH ⟨c, hcL⟩) = ψH (Subgroup.inclusion hCH ⟨c, hc⟩) := rfl
  rw [hψL, hψC, hψc] at h2
  have h3 : ψL (⟨l, hl⟩ * ⟨c, hcL⟩) = 1 := by
    apply Subgroup.inclusion_injective hL₀H₀
    rw [map_mul, map_mul, h2, mul_inv_cancel, map_one]
  have h4 : (⟨l, hl⟩ * ⟨c, hcL⟩ : ↥L) = 1 := (ψL.map_eq_one_iff).1 h3
  exact Subtype.ext (hlc.trans (by simpa using congrArg Subtype.val h4))

theorem exists_mulEquiv_of_sup_eq_of_card_eq {H L C : Subgroup X} {H₀ L₀ : Subgroup G₀}
    [Finite ↥H₀] (hLH : L ≤ H) (hCH : C ≤ H) (hHLC : L ⊔ C = H) (hLn : (L.subgroupOf H).Normal)
    (hL₀H₀ : L₀ ≤ H₀) (hL₀n : (L₀.subgroupOf H₀).Normal)
    (ψL : ↥L ≃* ↥L₀) (ψC : ↥C →* ↥H₀)
    (hagree : ∀ (x : X) (hxL : x ∈ L) (hxC : x ∈ C),
      Subgroup.inclusion hL₀H₀ (ψL ⟨x, hxL⟩) = ψC ⟨x, hxC⟩)
    (hrigid : ∀ α : ↥L₀ ≃* ↥L₀,
      (∀ (b : X) (hbL : b ∈ L), b ∈ C → α (ψL ⟨b, hbL⟩) = ψL ⟨b, hbL⟩) → α = MulEquiv.refl _)
    (hψCL : ∀ c : ↥C, ((ψC c : ↥H₀) : G₀) ∈ L₀ → (c : X) ∈ L)
    (hcard : Nat.card ↥H = Nat.card ↥H₀) :
    ∃ ψH : ↥H ≃* ↥H₀,
      (∀ l : ↥L, ψH (Subgroup.inclusion hLH l) = Subgroup.inclusion hL₀H₀ (ψL l)) ∧
      (∀ c : ↥C, ψH (Subgroup.inclusion hCH c) = ψC c) := by
  obtain ⟨ψH, hψL, hψC⟩ := exists_hom_of_sup_eq hLH hCH hHLC hLn hL₀H₀ hL₀n ψL ψC hagree hrigid
  have hinj := injective_of_restrict hLH hCH hHLC hLn hL₀H₀ ψL ψC ψH hψL hψC hψCL
  exact ⟨MulEquiv.ofBijective ψH ⟨hinj, (hinj.bijective_of_nat_card_le hcard.ge).2⟩, hψL, hψC⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
