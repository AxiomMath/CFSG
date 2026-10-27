module

public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.CGT.Timmesfeld75.Sec3Odd
public import CFSG.CGT.Timmesfeld75.Sec3Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Sec3Global (T : Subgroup G) : Prop :=
  ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
    Sec3 T (conjSubgroup g T)

theorem Sec3Global.of_inputs [Finite G] (hL214 : Lemma214) (hInv : InvolutionClassInput)
    {T : Subgroup G} (hT : IsWC T) : Sec3Global T :=
  fun _ hne hL => Sec3.of_inputs hL214 hInv hT hne hL

variable {T T₁ : Subgroup G}

theorem normIn_conjSubgroup_of_mem_normalizer {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G))
    (U : Subgroup G) : normIn T (conjSubgroup h U) = conjSubgroup h (normIn T U) := by
  have hT : conjSubgroup h T = T := mem_normalizer_iff_conjSubgroup_eq.1 hh
  have := normIn_conj h T U
  rwa [hT] at this

theorem MaxPair.conjSubgroup_ne (hP : MaxPair T T₁) {h : G}
    (hh : h ∈ Subgroup.normalizer (T : Set G)) : conjSubgroup h T₁ ≠ T := by
  intro heq
  apply hP.ne
  have hT : conjSubgroup h T = T := mem_normalizer_iff_conjSubgroup_eq.1 hh
  have h1 : conjSubgroup h⁻¹ (conjSubgroup h T₁) = T₁ := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have h2 : conjSubgroup h⁻¹ T = T :=
    mem_normalizer_iff_conjSubgroup_eq.1 ((Subgroup.normalizer (T : Set G)).inv_mem hh)
  rw [← h1, heq, h2]

theorem MaxPair.sec3_conj (hP : MaxPair T T₁) (hS : Sec3Global T) {h : G}
    (hh : h ∈ Subgroup.normalizer (T : Set G)) : Sec3 T (conjSubgroup h T₁) := by
  obtain ⟨x₀, hx₀⟩ := hP.conj
  have hconj : conjSubgroup h T₁ = conjSubgroup (h * x₀) T := by
    rw [hx₀, conjSubgroup_conjSubgroup]
  rw [hconj]
  refine hS (h * x₀) (by rw [← hconj]; exact hP.conjSubgroup_ne hh) ?_
  rw [← hconj, normIn_conjSubgroup_of_mem_normalizer hh]
  exact fun h0 => hP.nontriv (conjSubgroup_eq_bot_iff.1 h0)

theorem Cfg.inf_centralizer_normIn (c : Cfg T T₁) :
    T ⊓ Subgroup.centralizer (normIn T₁ T : Set G) = normIn T T₁ := by
  apply le_antisymm
  · rintro x ⟨hxT, hxC⟩
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.ne₁
    have hb1 : (b : G) ≠ 1 := fun h1 => hb (Subtype.ext h1)
    have hbT₁ : (b : G) ∈ T₁ := (mem_normIn.1 b.2).1
    have hxb : x ∈ Subgroup.centralizer ({(b : G)} : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun k hk => by
        rw [Set.mem_singleton_iff] at hk
        subst hk
        exact Subgroup.mem_centralizer_iff.1 hxC b b.2
    exact mem_normIn.2 ⟨hxT, c.wc₁.centralizer_le_normalizer hbT₁ hb1 hxb⟩
  · intro l hl
    refine ⟨normIn_le _ _ hl, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    exact (c.comm_L_L₁ hl hk).symm

section Swap

variable [Finite G]

theorem Sec3.exists_swap (hS : Sec3 T T₁) :
    ∃ s ∈ T ⊔ T₁, s * s = 1 ∧ conjSubgroup s T = T₁ ∧ conjSubgroup s T₁ = T := by
  obtain ⟨x₀, hx₀X, hx₀⟩ := hS.conj
  obtain ⟨a, haT, haM⟩ := IsConcreteLE.not_le_iff_exists.1 hS.not_le_cfgM
  obtain ⟨b, hbc, hbM⟩ := IsConcreteLE.not_le_iff_exists.1 (hS.not_conj_le_cfgM hx₀X)
  have hbT₁ : b ∈ T₁ := hx₀ ▸ hbc
  have hT₁ne : conjSubgroup 1 T ≠ conjSubgroup x₀ T := by
    rw [conjSubgroup_one, ← hx₀]
    exact hS.cfg.left_ne_right
  have haX : a ∈ T ⊔ T₁ := Subgroup.mem_sup_left haT
  have hbX : b ∈ T ⊔ T₁ := Subgroup.mem_sup_right hbT₁
  have haa : a * a = 1 := elemAbelian_mul_self hS.cfg.wc.1 haT
  have hbb : b * b = 1 := elemAbelian_mul_self hS.cfg.wc₁.1 hbT₁
  have hodd := hS.odd_orderOf_mul (one_mem _) hx₀X hT₁ne (by rwa [conjSubgroup_one]) haM hbc hbM
  obtain ⟨k, hk⟩ := hodd
  set w := a * b with hw
  have hinv : a * w * a⁻¹ = w⁻¹ := left_invol_inverts haa hbb
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hwn : w ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have hconj : a * w ^ k * a⁻¹ = (w ^ k)⁻¹ := by rw [← conj_pow, hinv, inv_pow]
  have hss : (w ^ k * a) * (w ^ k * a) = 1 := by
    calc (w ^ k * a) * (w ^ k * a) = w ^ k * (a * w ^ k * a⁻¹) := by rw [hainv]; group
      _ = 1 := by rw [hconj]; group
  have hsas : (w ^ k * a) * a * (w ^ k * a)⁻¹ = b := by
    have hsi : (w ^ k * a)⁻¹ = w ^ k * a := inv_eq_of_mul_eq_one_right hss
    rw [hsi]
    have h2k : w ^ (2 * k) = w⁻¹ := by
      have : w ^ (2 * k) * w = 1 := by rw [← pow_succ]; exact hwn
      exact eq_inv_of_mul_eq_one_left this
    calc w ^ k * a * a * (w ^ k * a) = w ^ k * (a * a) * w ^ k * a := by group
      _ = w ^ k * w ^ k * a := by rw [haa, mul_one]
      _ = w ^ (2 * k) * a := by rw [← pow_add, two_mul]
      _ = b := by
        rw [h2k, hw, mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right hbb]
  have hsX : w ^ k * a ∈ T ⊔ T₁ :=
    (T ⊔ T₁).mul_mem ((T ⊔ T₁).pow_mem ((T ⊔ T₁).mul_mem haX hbX) k) haX
  have hb1 : b ≠ 1 := fun h1 => hbM (h1 ▸ (cfgM T T₁).one_mem)
  have hbmem : b ∈ conjSubgroup (w ^ k * a) T := by
    rw [mem_conjSubgroup]
    have : (w ^ k * a)⁻¹ * b * (w ^ k * a) = a := by rw [← hsas]; group
    rwa [this]
  have hTs : conjSubgroup (w ^ k * a) T = T₁ := by
    have e : conjSubgroup ((w ^ k * a) * x₀⁻¹) T₁ = conjSubgroup (w ^ k * a) T := by
      rw [hx₀, conjSubgroup_conjSubgroup, show (w ^ k * a) * x₀⁻¹ * x₀ = w ^ k * a by group]
    have h1 : T₁ ⊓ conjSubgroup ((w ^ k * a) * x₀⁻¹) T₁ ≠ ⊥ := by
      rw [e]
      intro h0
      have : b ∈ T₁ ⊓ conjSubgroup (w ^ k * a) T := ⟨hbT₁, hbmem⟩
      rw [h0, Subgroup.mem_bot] at this
      exact hb1 this
    have h2 := hS.cfg.wc₁.conj_eq_of_inf_ne_bot h1
    rwa [e] at h2
  refine ⟨_, hsX, hss, hTs, ?_⟩
  rw [← hTs, conjSubgroup_conjSubgroup, hss, conjSubgroup_one]

theorem Sec3.card_normIn_swap (hS : Sec3 T T₁) :
    Nat.card (normIn T₁ T) = Nat.card (normIn T T₁) := by
  obtain ⟨s, -, -, hTs, hT₁s⟩ := hS.exists_swap
  have h := normIn_conj s T T₁
  rw [hTs, hT₁s] at h
  rw [h, card_conjSubgroup]

theorem Sec3.exists_mem_normIn₁_conj_eq (hS : Sec3 T T₁) {x u : G} (hx : x ∈ T)
    (hxM : x ∉ cfgM T T₁) (hu : u ∈ normIn T T₁) :
    ∃ l ∈ normIn T₁ T, l * x * l⁻¹ = x * u := by
  have hxX : x ∈ T ⊔ T₁ := Subgroup.mem_sup_left hx
  have hmem : ∀ l ∈ normIn T₁ T, x⁻¹ * (l * x * l⁻¹) ∈ normIn T T₁ := by
    intro l hl
    obtain ⟨hlT₁, hlN⟩ := mem_normIn.1 hl
    have hlM : l ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁ hl
    have h1 : l * x * l⁻¹ ∈ T := by
      have := conj_mem_of_mem_normalizer hlN hx
      exact this
    have h2 : x⁻¹ * (l * x * l⁻¹) ∈ T := T.mul_mem (T.inv_mem hx) h1
    have h3 : x⁻¹ * (l * x * l⁻¹) ∈ cfgM T T₁ := by
      have := hS.cfg.conj_mem_cfgM ((T ⊔ T₁).inv_mem hxX) hlM
      rw [inv_inv] at this
      have e : x⁻¹ * (l * x * l⁻¹) = (x⁻¹ * l * x) * l⁻¹ := by group
      rw [e]
      exact (cfgM T T₁).mul_mem this ((cfgM T T₁).inv_mem hlM)
    rw [← hS.cfg.inf_cfgM]
    exact ⟨h2, h3⟩
  let φ : normIn T₁ T → normIn T T₁ := fun l => ⟨x⁻¹ * (l * x * l⁻¹), hmem l l.2⟩
  have hinj : Function.Injective φ := by
    intro l l' hll
    have h1 : x⁻¹ * ((l : G) * x * (l : G)⁻¹) = x⁻¹ * ((l' : G) * x * (l' : G)⁻¹) :=
      congrArg Subtype.val hll
    have h2 := mul_left_cancel h1
    have hcomm : x * ((l' : G)⁻¹ * l) = ((l' : G)⁻¹ * l) * x := by
      have : (l : G) * x = (l' : G) * x * (l' : G)⁻¹ * l := by
        have h3 := congrArg (fun z => z * (l : G)) h2
        simpa [mul_assoc] using h3
      calc x * ((l' : G)⁻¹ * l) = (l' : G)⁻¹ * ((l' : G) * x * (l' : G)⁻¹ * l) := by group
        _ = (l' : G)⁻¹ * ((l : G) * x) := by rw [this]
        _ = ((l' : G)⁻¹ * l) * x := by group
    have hmem1 : (l' : G)⁻¹ * l ∈ normIn T₁ T :=
      (normIn T₁ T).mul_mem ((normIn T₁ T).inv_mem l'.2) l.2
    have hmemC : (l' : G)⁻¹ * l ∈ cfgM T T₁ ⊓ Subgroup.centralizer ({x} : Set G) :=
      ⟨Cfg.normIn_le_cfgM_right T T₁ hmem1, Subgroup.mem_centralizer_iff.2 fun k hk => by
        rw [Set.mem_singleton_iff] at hk
        subst hk
        exact hcomm⟩
    rw [hS.cfg.cfgM_inf_centralizer hx hxM] at hmemC
    have hbot : (l' : G)⁻¹ * l ∈ T ⊓ T₁ := ⟨normIn_le _ _ hmemC, normIn_le _ _ hmem1⟩
    rw [hS.cfg.inf, Subgroup.mem_bot, inv_mul_eq_one] at hbot
    exact Subtype.ext hbot.symm
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hS.card_normIn_swap])
  obtain ⟨l, hl⟩ := hbij.2 ⟨u, hu⟩
  refine ⟨l, l.2, ?_⟩
  have h1 : x⁻¹ * ((l : G) * x * (l : G)⁻¹) = u := congrArg Subtype.val hl
  calc (l : G) * x * (l : G)⁻¹ = x * (x⁻¹ * ((l : G) * x * (l : G)⁻¹)) := by group
    _ = x * u := by rw [h1]

end Swap

end CFSG.CGT.Timmesfeld75
