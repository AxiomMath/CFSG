module

public import CFSG.CGT.T75M.StageA2

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {a : ℕ}

section Normal

omit [Finite G] in
theorem conj_normIn_eq (hD : SzData T T₁ a)
    (hB : ∀ h ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup h (normIn T₁ T) ≤ normIn T₁ T ⊔ T)
    {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup h (normIn T T₁) = normIn T T₁ := by
  have hS := hD.sec3
  have hcfg := hS.cfg
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hxh : h * x * h⁻¹ ∈ conjSubgroup h (normIn T₁ T) := by
    rw [mem_conjSubgroup]
    have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rw [e]; exact hx
  have hmem := hB h hh hxh
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T₁ T) T
    (fun y hy => (mem_normIn.1 hy).2)
  rw [← SetLike.mem_coe, hset] at hmem
  obtain ⟨l, hl, τ, hτ, hlτ⟩ := Set.mem_mul.1 hmem
  have hl1 : l ≠ 1 := by
    intro hl1
    rw [hl1, one_mul] at hlτ
    have h3 : h⁻¹ * τ * (h⁻¹)⁻¹ ∈ T :=
      conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hh) hτ
    rw [inv_inv, hlτ] at h3
    have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rw [e] at h3
    have h4 : x ∈ T ⊓ T₁ := Subgroup.mem_inf.2 ⟨h3, normIn_le _ _ hx⟩
    rw [hcfg.inf, Subgroup.mem_bot] at h4
    exact hx1' h4
  have h1 := inf_centralizer_conj hcfg hx hx1' hh
  have h2 := inf_centralizer_eq_normIn hcfg hl hl1
  rw [← h1, ← hlτ, ← h2]
  ext z
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hz => ?_
  have hτz : τ * z = z * τ := elemAbelian_mul_comm hcfg.wc.1 hτ hz
  constructor
  · intro hc
    have h3 : z * l * τ = l * z * τ :=
      calc z * l * τ = z * (l * τ) := mul_assoc z l τ
        _ = l * τ * z := hc
        _ = l * (τ * z) := mul_assoc l τ z
        _ = l * (z * τ) := by rw [hτz]
        _ = l * z * τ := (mul_assoc l z τ).symm
    exact mul_right_cancel h3
  · intro hc
    calc z * (l * τ) = z * l * τ := (mul_assoc z l τ).symm
      _ = l * z * τ := by rw [hc]
      _ = l * (z * τ) := mul_assoc l z τ
      _ = l * (τ * z) := by rw [hτz]
      _ = l * τ * z := (mul_assoc l τ z).symm

omit [Finite G] in
theorem conj_normIn_le_cfgM (hD : SzData T T₁ a)
    (hB : ∀ h ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup h (normIn T₁ T) ≤ normIn T₁ T ⊔ T)
    {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup h (normIn T₁ T) ≤ cfgM T T₁ := by
  have hS := hD.sec3
  have hcfg := hS.cfg
  intro y hy
  have hy2 : y * y = 1 := elemAbelian_mul_self
    (isElemAbelian_conjSubgroup (isElemAbelian_of_le' hcfg.wc₁.1 (normIn_le T₁ T)) h) hy
  have hmem := hB h hh hy
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T₁ T) T
    (fun y hy => (mem_normIn.1 hy).2)
  rw [← SetLike.mem_coe, hset] at hmem
  obtain ⟨l, hl, τ, hτ, rfl⟩ := Set.mem_mul.1 hmem
  by_cases hl1 : l = 1
  · subst hl1
    have hyT : (1 : G) * τ ∈ T := by simpa using hτ
    have h1 : h⁻¹ * (1 * τ) * h ∈ normIn T₁ T := mem_conjSubgroup.1 hy
    have h2 : h⁻¹ * (1 * τ) * h ∈ T := by
      have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hh) hyT
      rwa [inv_inv] at this
    have h3 : h⁻¹ * (1 * τ) * h ∈ T ⊓ T₁ := Subgroup.mem_inf.2 ⟨h2, normIn_le _ _ h1⟩
    rw [hcfg.inf, Subgroup.mem_bot] at h3
    have h4 : (1 : G) * τ = 1 := by
      have e : (1 : G) * τ = h * (h⁻¹ * (1 * τ) * h) * h⁻¹ := by group
      rw [e, h3]; group
    rw [h4]
    exact (cfgM T T₁).one_mem
  · have hl2 : l * l = 1 := elemAbelian_mul_self hcfg.wc₁.1 (normIn_le _ _ hl)
    have hτ2 : τ * τ = 1 := elemAbelian_mul_self hcfg.wc.1 hτ
    have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl2
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
    have h2 : l * τ = τ * l := by
      have := eq_inv_of_mul_eq_one_left hy2
      rwa [mul_inv_rev, hτi, hli] at this
    have hτL : τ ∈ normIn T T₁ := by
      rw [← inf_centralizer_eq_normIn hcfg hl hl1]
      exact Subgroup.mem_inf.2 ⟨hτ, Subgroup.mem_centralizer_singleton_iff.2 h2.symm⟩
    exact (cfgM T T₁).mul_mem (Cfg.normIn_le_cfgM_right T T₁ hl)
      (Cfg.normIn_le_cfgM_left T T₁ hτL)

theorem mem_normalizer_cfgM (hD : SzData T T₁ a)
    (hB : ∀ h ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup h (normIn T₁ T) ≤ normIn T₁ T ⊔ T)
    {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    h ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq]
  refine conjSubgroup_eq_of_le ?_
  have : conjSubgroup h (cfgM T T₁) = normIn T T₁ ⊔ conjSubgroup h (normIn T₁ T) := by
    rw [cfgM, conjSubgroup_sup_eq_sup, conj_normIn_eq hD hB hh]
  rw [this]
  exact sup_le (Cfg.normIn_le_cfgM_left T T₁) (conj_normIn_le_cfgM hD hB hh)

theorem mem_normalizer_sup (hKL : SzTriangleInput)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hD : SzData T T₁ a)
    (hB : ∀ h ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup h (normIn T₁ T) ≤ normIn T₁ T ⊔ T)
    {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    h ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G) := by
  have hcfg := hD.sec3.cfg
  have hL := conj_normIn_eq hD hB hh
  have hle := conj_normIn_le_cfgM hD hB hh
  have hM := mem_normalizer_cfgM hD hB hh
  have hN : normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup h (normIn T₁ T) = cfgM T T₁ :=
    sup_eq_left.2 hle
  have hel : IsElemAbelian 2 (normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup h (normIn T₁ T)) := by
    rw [hN]; exact hcfg.isElemAbelian_cfgM
  have hT₁' : ∀ y ∈ conjSubgroup h T₁,
      y ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) := by
    intro y hy
    have ht : h⁻¹ * y * h ∈ T₁ := mem_conjSubgroup.1 hy
    have htN := hcfg.le_normalizer_cfgM (Subgroup.mem_sup_right ht)
    have h1 : h * (h⁻¹ * y * h) * h⁻¹ ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) :=
      (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hM htN)
        ((Subgroup.normalizer _).inv_mem hM)
    rwa [show h * (h⁻¹ * y * h) * h⁻¹ = y by group] at h1
  have hnorm : ∀ y ∈ T ⊔ T₁ ⊔ conjSubgroup h T₁,
      ∀ n ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup h (normIn T₁ T),
        y * n * y⁻¹ ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ conjSubgroup h (normIn T₁ T) := by
    rw [hN]
    intro y hy n hn
    have hle' : T ⊔ T₁ ⊔ conjSubgroup h T₁ ≤
        Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) :=
      sup_le hcfg.le_normalizer_cfgM hT₁'
    exact (Subgroup.mem_normalizer_iff.1 (hle' hy) n).1 hn
  have hle' := hKL G hnab T T₁ a hD h hh hL hel hnorm
  rw [mem_normalizer_iff_conjSubgroup_eq]
  refine conjSubgroup_eq_of_le ?_
  rw [conjSubgroup_sup_eq_sup, mem_normalizer_iff_conjSubgroup_eq.1 hh]
  exact sup_le le_sup_left hle'

end Normal

section Comm

theorem exists_comm_eq (hS : Sec3 T T₁) {t : G} (htT : t ∈ T) (htM : t ∉ cfgM T T₁) :
    ∀ ℓ ∈ normIn T T₁, ∃ u ∈ normIn T₁ T, ⁅u, t⁆ = ℓ := by
  have hcfg := hS.cfg
  have hcomm_mem : ∀ u ∈ normIn T₁ T, ⁅u, t⁆ ∈ normIn T T₁ := fun u hu => by
    have h2 := (normIn T T₁).inv_mem (hcfg.comm_mem_normIn htT hu)
    rwa [commutatorElement_inv] at h2
  let χ : ↥(normIn T₁ T) →* ↥(normIn T T₁) :=
    MonoidHom.mk' (fun u => ⟨⁅(u : G), t⁆, hcomm_mem u u.2⟩) (fun u u' => by
      apply Subtype.ext
      show ⁅(u : G) * u', t⁆ = ⁅(u : G), t⁆ * ⁅(u' : G), t⁆
      have hcu : ⁅(u' : G), t⁆ * u = u * ⁅(u' : G), t⁆ :=
        hcfg.comm_L_L₁ (hcomm_mem u' u'.2) u.2
      have e1 : (u' : G) * t * (u' : G)⁻¹ = ⁅(u' : G), t⁆ * t := by
        simp only [commutatorElement_def]; group
      have e2 : (u : G) * ⁅(u' : G), t⁆ * (u : G)⁻¹ = ⁅(u' : G), t⁆ := by
        rw [← hcu]; group
      have habel : ⁅(u' : G), t⁆ * ⁅(u : G), t⁆ = ⁅(u : G), t⁆ * ⁅(u' : G), t⁆ :=
        elemAbelian_mul_comm (isElemAbelian_of_le' hcfg.wc.1 (normIn_le T T₁))
          (hcomm_mem u' u'.2) (hcomm_mem u u.2)
      calc ⁅(u : G) * u', t⁆
          = (u : G) * ((u' : G) * t * (u' : G)⁻¹) * (u : G)⁻¹ * t⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = (u : G) * (⁅(u' : G), t⁆ * t) * (u : G)⁻¹ * t⁻¹ := by rw [e1]
        _ = ((u : G) * ⁅(u' : G), t⁆ * (u : G)⁻¹) * ((u : G) * t * (u : G)⁻¹ * t⁻¹) := by group
        _ = ⁅(u' : G), t⁆ * ⁅(u : G), t⁆ := by rw [e2]; rfl
        _ = ⁅(u : G), t⁆ * ⁅(u' : G), t⁆ := habel)
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : ⁅(u : G), t⁆ = 1 := congrArg Subtype.val hu
    have h2 : (u : G) ∈ cfgM T T₁ ⊓ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_inf.2 ⟨Cfg.normIn_le_cfgM_right T T₁ u.2,
        Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h1)⟩
    rw [hcfg.cfgM_inf_centralizer htT htM] at h2
    have h3 : (u : G) ∈ T ⊓ T₁ := Subgroup.mem_inf.2 ⟨normIn_le _ _ h2, normIn_le _ _ u.2⟩
    rw [hcfg.inf, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hbij : Function.Bijective χ :=
    hinj.bijective_of_nat_card_le (card_normIn_right hS).ge
  intro ℓ hℓ
  obtain ⟨u, hu⟩ := hbij.2 ⟨ℓ, hℓ⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem comm_mem_normIn_of_normalizes (hD : SzData T T₁ a) {u : G}
    (huX : u ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G))
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G))
    (huT : u ∈ Subgroup.normalizer (T : Set G)) (hu2 : u * u = 1) :
    ∀ t ∈ T, ⁅u, t⁆ ∈ normIn T T₁ := by
  have hcfg := hD.sec3.cfg
  obtain ⟨y, hyT, hy, -⟩ := hD.exists_comm_of_normalizes huX huM huT hu2
  intro t ht
  have hw : u * t * u⁻¹ ∈ T := conj_mem_of_mem_normalizer huT ht
  have h1 := hy t (Subgroup.mem_sup_left ht)
  have hyw : y * (u * t * u⁻¹) = (u * t * u⁻¹) * y := elemAbelian_mul_comm hcfg.wc.1 hyT hw
  have e : ⁅y * u, t⁆ = ⁅u, t⁆ :=
    calc ⁅y * u, t⁆ = y * (u * t * u⁻¹) * y⁻¹ * t⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (u * t * u⁻¹) * y * y⁻¹ * t⁻¹ := by rw [hyw]
      _ = ⁅u, t⁆ := by simp only [commutatorElement_def]; group
  rw [e] at h1
  have h2 : ⁅u, t⁆ ∈ T := by
    have : ⁅u, t⁆ = (u * t * u⁻¹) * t⁻¹ := by simp only [commutatorElement_def]
    rw [this]; exact T.mul_mem hw (T.inv_mem ht)
  rw [← hcfg.inf_cfgM]
  exact Subgroup.mem_inf.2 ⟨h2, h1⟩

end Comm

end CFSG.CGT.T75M
