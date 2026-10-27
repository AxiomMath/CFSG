module

public import CFSG.CGT.T75M.StageA2
public import CFSG.CGT.Timmesfeld75.Sec3Six

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

section Helpers

variable [Finite G] {T T₁ : Subgroup G} {a : ℕ}

omit [Finite G] in
theorem conj_normIn_le_cfgM_of_le [Finite G] (hD : SzData T T₁ a) {c : G}
    (hc : c ∈ Subgroup.normalizer (T : Set G)) (hle : conjSubgroup c T₁ ≤ T ⊔ T₁) :
    conjSubgroup c (normIn T₁ T) ≤ cfgM T T₁ := by
  have hS := hD.sec3
  have hcfg := hS.cfg
  have hcT : conjSubgroup c T = T := mem_normalizer_iff_conjSubgroup_eq.1 hc
  obtain ⟨x₁, hx₁, hT₁⟩ := hS.conj
  have hT₂eq : conjSubgroup c T₁ = conjSubgroup (c * x₁) T := by
    rw [hT₁, conjSubgroup_conjSubgroup]
  obtain ⟨x, hx, hxeq⟩ := exists_mem_conj_eq_of_le hcfg.wc (le_sup_left : T ≤ T ⊔ T₁)
    (g := c * x₁) (hT₂eq ▸ hle)
  have hne : conjSubgroup x T ≠ conjSubgroup 1 T := by
    rw [conjSubgroup_one, ← hxeq, ← hT₂eq]
    intro h
    apply hcfg.left_ne_right
    have h2 : conjSubgroup c⁻¹ (conjSubgroup c T₁) = conjSubgroup c⁻¹ T := by rw [h]
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2
    rw [h2]
    exact (mem_normalizer_iff_conjSubgroup_eq.1 (inv_mem hc)).symm
  have h1 := hS.normIn_conj_eq hx (T ⊔ T₁).one_mem hne
  rw [conjSubgroup_one] at h1
  have hL₁₂ : conjSubgroup c (normIn T₁ T) = normIn (conjSubgroup c T₁) T := by
    have := normIn_conj c T₁ T
    rw [hcT] at this
    exact this.symm
  rw [hL₁₂, hT₂eq, hxeq, h1]
  exact hcfg.conjSubgroup_normIn_le_cfgM hx


omit [Finite G] in
theorem comm_mem_of_mul_mem (hS : Sec3 T T₁) {y u : G} (hy : y ∈ cfgM T T₁)
    (h : ∀ x ∈ T ⊔ T₁, ⁅y * u, x⁆ ∈ cfgM T T₁) : ∀ x ∈ T ⊔ T₁, ⁅u, x⁆ ∈ cfgM T T₁ := by
  intro x hx
  have h1 := h x hx
  have h2 : x * y * x⁻¹ ∈ cfgM T T₁ := hS.cfg.conj_mem_cfgM hx hy
  have e : ⁅u, x⁆ = y⁻¹ * ⁅y * u, x⁆ * (x * y * x⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (cfgM T T₁).mul_mem ((cfgM T T₁).mul_mem ((cfgM T T₁).inv_mem hy) h1) h2

end Helpers


section Main

variable [Finite G] {T T₁ : Subgroup G} {a : ℕ}

theorem strongly_closed_L₁ (hKL : SzTriangleInput)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hD : SzData T T₁ a) {h : G}
    (hh : h ∈ Subgroup.normalizer (T : Set G)) {x : G} (hx : x ∈ normIn T₁ T) {t : G}
    (ht : t ∈ normIn T₁ T) (ht1 : t ≠ 1) (hcomm : ⁅h * x * h⁻¹, t⁆ ∈ T) :
    h * x * h⁻¹ ∈ normIn T₁ T ⊔ T := by
  classical
  by_contra hd
  have hS := hD.sec3
  have hcfg := hS.cfg
  have hx1 : x ≠ 1 := fun h1 => hd (by rw [h1]; simp)
  set d : G := h * x * h⁻¹ with hddef
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hx).2
  have hdN : d ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hh hxN)
      ((Subgroup.normalizer (T : Set G)).inv_mem hh)
  have hx2 : x * x = 1 := elemAbelian_mul_self hcfg.wc₁.1 (normIn_le _ _ hx)
  have hd2 : d * d = 1 := by
    calc d * d = h * (x * x) * h⁻¹ := by simp only [hddef]; group
      _ = 1 := by rw [hx2]; group
  have hd1 : d ≠ 1 := fun h1 => hx1 (by
    have e : x = h⁻¹ * d * h := by simp only [hddef]; group
    rw [e, h1]; group)
  have hdL₁' : d ∈ conjSubgroup h (normIn T₁ T) := by
    rw [mem_conjSubgroup]
    have e : h⁻¹ * d * h = x := by simp only [hddef]; group
    rw [e]; exact hx
  have hidxd : Nat.card T ≤
      2 ^ (2 * a + 1) * Nat.card ↥(T ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [card_inf_centralizer_conj hcfg hx hx1 hh, hD.card_eq_mul, mul_comm]
  have hMLL : cfgM T T₁ ≤ normIn T₁ T ⊔ T :=
    sup_le (le_trans (normIn_le T T₁) le_sup_right) le_sup_left
  by_cases hdt : d * t = t * d
  ·
    have hdT₁ : d ∈ Subgroup.normalizer (T₁ : Set G) :=
      hcfg.wc₁.centralizer_le_normalizer (normIn_le _ _ ht) ht1
        (Subgroup.mem_centralizer_singleton_iff.2 hdt)
    have hMd : ∀ m ∈ cfgM T T₁, m * d = d * m :=
      (hD.centralizes_of_normalizes hdN hdT₁ hd2 hidxd).2
    have hcT : conjSubgroup h T = T := mem_normalizer_iff_conjSubgroup_eq.1 hh
    have hL₁₂ : conjSubgroup h (normIn T₁ T) = normIn (conjSubgroup h T₁) T := by
      have := normIn_conj h T₁ T
      rw [hcT] at this
      exact this.symm
    have hdT₂ : d ∈ conjSubgroup h T₁ := normIn_le _ _ (hL₁₂ ▸ hdL₁')
    have hN : ∀ x' ∈ normIn T₁ T,
        x' ∈ Subgroup.normalizer ((conjSubgroup h T₁ : Subgroup G) : Set G) := fun x' hx' =>
      (hcfg.wc₁.conj h).centralizer_le_normalizer hdT₂ hd1
        (Subgroup.mem_centralizer_singleton_iff.2 (hMd x' (Cfg.normIn_le_cfgM_right T T₁ hx')))
    have hP2 := p2_of_normalizes hD hh hN
    have hP1 := p1_of_p2 hD hh (fun x' hx' => (hP2 x' hx').2)
    have hle := conj_le_of_p1 hKL hnab hD hh hP1
    have hdM : d ∈ cfgM T T₁ := conj_normIn_le_cfgM_of_le hD hh hle hdL₁'
    exact hd (hMLL hdM)
  ·
    have hℓ1 : ⁅d, t⁆ ≠ 1 := fun h1 => hdt (commutatorElement_eq_one_iff_mul_comm.1 h1)
    have htt : t * t = 1 := elemAbelian_mul_self hcfg.wc₁.1 (normIn_le _ _ ht)
    have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hℓdef : ⁅d, t⁆ = d * t * d * t := by rw [commutatorElement_def, hdi, hti]
    have hℓinv : ⁅d, t⁆⁻¹ = ⁅d, t⁆ := elemAbelian_inv hcfg.wc.1 hcomm
    have htℓ : t * ⁅d, t⁆ = ⁅d, t⁆ * t := by
      have h1 : t * ⁅d, t⁆ * t = ⁅d, t⁆ := by
        calc t * ⁅d, t⁆ * t = t * d * t * d * (t * t) := by rw [hℓdef]; simp only [mul_assoc]
          _ = t * d * t * d := by rw [htt, mul_one]
          _ = ⁅d, t⁆⁻¹ := by rw [commutatorElement_inv, commutatorElement_def, hti, hdi]
          _ = ⁅d, t⁆ := hℓinv
      calc t * ⁅d, t⁆ = t * ⁅d, t⁆ * (t * t) := by rw [htt, mul_one]
        _ = (t * ⁅d, t⁆ * t) * t := by simp only [mul_assoc]
        _ = ⁅d, t⁆ * t := by rw [h1]
    have hℓL : ⁅d, t⁆ ∈ normIn T T₁ := by
      rw [← inf_centralizer_eq_normIn hcfg ht ht1]
      exact ⟨hcomm, Subgroup.mem_centralizer_singleton_iff.2 htℓ.symm⟩
    have ht' : d * t * d⁻¹ = ⁅d, t⁆ * t := by simp only [commutatorElement_def]; group
    have ht'mem : d * t * d⁻¹ ∈ conjSubgroup d (normIn T₁ T) ⊓ (normIn T₁ T ⊔ T) := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_conjSubgroup]
        have e : d⁻¹ * (d * t * d⁻¹) * d = t := by group
        rw [e]; exact ht
      · rw [ht']
        exact (normIn T₁ T ⊔ T).mul_mem (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left ht)
    have ht'1 : d * t * d⁻¹ ≠ 1 := fun h1 => ht1 (by
      have e : t = d⁻¹ * (d * t * d⁻¹) * d := by group
      rw [e, h1]; group)
    have hne : conjSubgroup d (normIn T₁ T) ⊓ (normIn T₁ T ⊔ T) ≠ ⊥ := fun hbot => ht'1 (by
      have := ht'mem
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this)
    obtain ⟨h36a, h36b⟩ := hcfg.commute_conj_L₁ hdN hne
    obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
    have hx₀1' : x₀ ≠ 1 := fun h1 => hx₀1 (Subtype.ext h1)
    have hP1 : ∀ u ∈ conjSubgroup d (normIn T₁ T), u ∈ Subgroup.normalizer (T₁ : Set G) ∧
        ∀ m ∈ cfgM T T₁, m * u = u * m := by
      intro u hu
      refine ⟨hcfg.wc₁.centralizer_le_normalizer (normIn_le _ _ hx₀) hx₀1'
        (Subgroup.mem_centralizer_singleton_iff.2 (h36a u hu x₀ hx₀)), fun m hm => ?_⟩
      obtain ⟨l, hl, x', hx', rfl⟩ := hcfg.mem_cfgM_iff.1 hm
      have h1 : u * l = l * u := h36b u hu l hl
      have h2 : u * x' = x' * u := h36a u hu x' hx'
      calc l * x' * u = l * (x' * u) := by rw [mul_assoc]
        _ = l * (u * x') := by rw [h2]
        _ = (l * u) * x' := by rw [mul_assoc]
        _ = (u * l) * x' := by rw [h1]
        _ = u * (l * x') := by rw [mul_assoc]
    have hle := conj_le_of_p1 hKL hnab hD hdN hP1
    have hL₁'M := conj_normIn_le_cfgM_of_le hD hdN hle
    have hNd := normalizes_of_p1 hD hdN hP1
    have hP2d := p2_of_normalizes hD hdN hNd
    have hLLd := conj_normIn_eq_of_p2 hD hdN (fun x' hx' => (hP2d x' hx').2)
    have hdM : d ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff_conjSubgroup_eq]
      refine conjSubgroup_eq_of_le ?_
      have : conjSubgroup d (cfgM T T₁) = normIn T T₁ ⊔ conjSubgroup d (normIn T₁ T) := by
        rw [cfgM, conjSubgroup_sup_eq_sup, hLLd]
      rw [this]
      exact sup_le (Cfg.normIn_le_cfgM_left T T₁) hL₁'M
    have hdX : d ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff_conjSubgroup_eq]
      refine conjSubgroup_eq_of_le ?_
      rw [conjSubgroup_sup_eq_sup, mem_normalizer_iff_conjSubgroup_eq.1 hdN]
      exact sup_le le_sup_left hle
    obtain ⟨y, hyT, hy, -⟩ := hD.exists_comm_of_normalizes hdX hdM hdN hd2
    have hyX : y ∈ T ⊔ T₁ := Subgroup.mem_sup_left hyT
    have hyM : y ∉ cfgM T T₁ := by
      intro hyM
      have hX' : ∀ z ∈ T ⊔ T₁, ⁅d, z⁆ ∈ cfgM T T₁ := comm_mem_of_mul_mem hS hyM hy
      have := hD.comm_of_index_le hdM (fun z hz => by
          have := (cfgM T T₁).inv_mem (hX' z hz)
          rwa [commutatorElement_inv] at this) hidxd
      exact hdt (this t (Cfg.normIn_le_cfgM_right T T₁ ht)).symm
    have hyy : y * y = 1 := elemAbelian_mul_self hcfg.wc.1 hyT
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    have hu'M : y * d ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) :=
      (Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G)).mul_mem
        (hcfg.le_normalizer_cfgM hyX) hdM
    have hydcomm : ∀ x ∈ T ⊔ T₁, ⁅x, y * d⁆ ∈ cfgM T T₁ := fun x hx => by
      have := (cfgM T T₁).inv_mem (hy x hx)
      rwa [commutatorElement_inv] at this
    have hyc : ∀ z ∈ T, (z * (y * d) = y * d * z ↔ z * d = d * z) := fun z hz => by
      have hyz : y * z = z * y := elemAbelian_mul_comm hcfg.wc.1 hyT hz
      constructor
      · intro h
        have h1 : y * (z * d) = y * (d * z) :=
          calc y * (z * d) = y * z * d := (mul_assoc y z d).symm
            _ = z * y * d := by rw [hyz]
            _ = z * (y * d) := mul_assoc z y d
            _ = y * d * z := h
            _ = y * (d * z) := mul_assoc y d z
        exact mul_left_cancel h1
      · intro h
        calc z * (y * d) = z * y * d := (mul_assoc z y d).symm
          _ = y * z * d := by rw [hyz]
          _ = y * (z * d) := mul_assoc y z d
          _ = y * (d * z) := by rw [h]
          _ = y * d * z := (mul_assoc y d z).symm
    have hCT : T ⊓ Subgroup.centralizer ({y * d} : Set G) =
        T ⊓ Subgroup.centralizer ({d} : Set G) := by
      ext z
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      exact and_congr_right fun hz => hyc z hz
    have hidx' : Nat.card T ≤
        2 ^ (2 * a + 1) * Nat.card ↥(T ⊓ Subgroup.centralizer ({y * d} : Set G)) := by
      rw [hCT]; exact hidxd
    have hcent : ∀ m ∈ cfgM T T₁, m * (y * d) = y * d * m :=
      hD.comm_of_index_le hu'M hydcomm hidx'
    have hLC : normIn T T₁ ≤ T ⊓ Subgroup.centralizer ({d} : Set G) := fun z hz => by
      have hzT : z ∈ T := normIn_le _ _ hz
      refine Subgroup.mem_inf.2 ⟨hzT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (hyc z hzT).1 (hcent z (Cfg.normIn_le_cfgM_left T T₁ hz))
    have hCTeq : normIn T T₁ = T ⊓ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hLC (card_inf_centralizer_conj hcfg hx hx1 hh).le
    have hyL : y ∉ T ⊓ Subgroup.centralizer ({d} : Set G) := fun hyC => hyM (by
      rw [← hCTeq] at hyC
      exact Cfg.normIn_le_cfgM_left T T₁ hyC)
    have hw : ⁅y * d, y⁆ = y * d * (y * d) := by
      simp only [commutatorElement_def, mul_inv_rev, hyi, hdi]
      simp only [mul_assoc, hyy, mul_one]
    have hwM : y * d * (y * d) ∈ cfgM T T₁ := by rw [← hw]; exact hy y hyX
    have hw1 : y * d * (y * d) ≠ 1 := by
      intro h1
      have h2 : y * d = (y * d)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [mul_inv_rev, hyi, hdi] at h2
      exact hyL (Subgroup.mem_inf.2 ⟨hyT, Subgroup.mem_centralizer_singleton_iff.2 h2⟩)
    have hwX : ∀ x ∈ T ⊔ T₁, x * (y * d * (y * d)) = y * d * (y * d) * x := by
      intro x hx
      have hm := hydcomm x hx
      have hmm : ⁅x, y * d⁆ * ⁅x, y * d⁆ = 1 :=
        elemAbelian_mul_self hcfg.isElemAbelian_cfgM hm
      have hmu : ⁅x, y * d⁆ * (y * d) = y * d * ⁅x, y * d⁆ := hcent _ hm
      have hconj : x * (y * d) * x⁻¹ = ⁅x, y * d⁆ * (y * d) := by
        simp only [commutatorElement_def]; group
      have h3 : x * (y * d * (y * d)) * x⁻¹ = y * d * (y * d) := by
        calc x * (y * d * (y * d)) * x⁻¹
            = (x * (y * d) * x⁻¹) * (x * (y * d) * x⁻¹) := by group
          _ = (⁅x, y * d⁆ * (y * d)) * (⁅x, y * d⁆ * (y * d)) := by rw [hconj]
          _ = ⁅x, y * d⁆ * ((y * d) * ⁅x, y * d⁆) * (y * d) := by simp only [mul_assoc]
          _ = ⁅x, y * d⁆ * (⁅x, y * d⁆ * (y * d)) * (y * d) := by rw [hmu]
          _ = (⁅x, y * d⁆ * ⁅x, y * d⁆) * (y * d * (y * d)) := by simp only [mul_assoc]
          _ = y * d * (y * d) := by rw [hmm, one_mul]
      calc x * (y * d * (y * d)) = x * (y * d * (y * d)) * x⁻¹ * x := by group
        _ = y * d * (y * d) * x := by rw [h3]
    exact hw1 (eq_bot_of_forall_comm hS hwM hwX)

end Main

end CFSG.CGT.T75M
