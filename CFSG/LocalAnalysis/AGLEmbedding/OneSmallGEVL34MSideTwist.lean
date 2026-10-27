module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideUniq

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {Y : Type} [Group Y] [Finite Y]

theorem L34MSide.false_of_bad {z : Y} {R T : Subgroup Y}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hconj : ∀ y ∈ Subgroup.centralizer ({z} : Set Y), IsPGroup 3 (Subgroup.zpowers y) →
      ∃ c ∈ Subgroup.centralizer ({z} : Set Y), c⁻¹ * y * c ∈ R)
    (hfus : ∀ r ∈ R, r ∉ T → ∃ n : Y, n * r * n⁻¹ ∈ Subgroup.zpowers z)
    (htr : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * t * n⁻¹ = s)
    (htrz : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = s)
    (hT9 : Nat.card T = 9)
    (hzcomp : ∀ L : Subgroup Y, IsComponentOf L ⊤ → z ∉ Subgroup.centralizer (L : Set Y))
    (hcen : ∀ L : Subgroup Y, IsComponentOf L ⊤ → ∀ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) →
      y * z = z * y → ∀ l ∈ L, y * l = l * y)
    (htwist : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      ∃ h ∈ L, h ^ 3 = 1 ∧ ∃ c ∈ L, z * h * z⁻¹ = c * h ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧ c * z = z * c ∧
        ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) ↔ x ∈ Subgroup.zpowers c)
    (hcomp : ∃ L : Subgroup Y, IsComponentOf L ⊤) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm_ne : ∀ {A B : Subgroup Y}, IsComponentOf A ⊤ → IsComponentOf B ⊤ → A ≠ B →
      ∀ {x : Y}, x ∈ B → ∀ l ∈ A, x * l = l * x :=
    fun hA hB hne _ hx => L34MSide.comm_of_mem_two hA hB hne hx
  obtain ⟨L, hL⟩ := hcomp
  obtain ⟨-, -, -, c₀, hc₀L, -, hc₀1, hc₀3, hc₀z, hZ₀⟩ := htwist L hL
  have hc₀c : ∀ l ∈ L, c₀ * l = l * c₀ := (hZ₀ c₀ hc₀L).mpr (Subgroup.mem_zpowers c₀)
  have hc₀C : c₀ ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀z
  obtain ⟨d, -, hdR⟩ := hconj c₀ hc₀C (L34MSide.isPGroup_zpowers_of_pow_three hc₀3)
  set L₁ := L.map (MulAut.conj d⁻¹).toMonoidHom with hL₁def
  have hL₁ : IsComponentOf L₁ ⊤ := isComponentOf_map_conj hL d⁻¹
  obtain ⟨h₁, hh₁L, hh₁3, c, hcL, hzh₁, hc1, hc3, hcz, hZ₁⟩ := htwist L₁ hL₁
  have hcc : ∀ l ∈ L₁, c * l = l * c := (hZ₁ c hcL).mpr (Subgroup.mem_zpowers c)
  have hd' : d⁻¹ * c₀ * d ∈ L₁ := by
    have := conj_mem_map_conj d⁻¹ hc₀L
    rwa [inv_inv] at this
  have hd'c : ∀ l ∈ L₁, d⁻¹ * c₀ * d * l = l * (d⁻¹ * c₀ * d) := by
    have := L34MSide.central_conj hc₀c d⁻¹
    simpa only [inv_inv] using this
  have hd'1 : d⁻¹ * c₀ * d ≠ 1 := by
    intro h
    apply hc₀1
    have := congrArg (fun v => d * v * d⁻¹) h
    simpa [mul_assoc] using this
  have hd'z : d⁻¹ * c₀ * d ∈ Subgroup.zpowers c := (hZ₁ _ hd').mp hd'c
  have hcR : c ∈ R :=
    (Subgroup.zpowers_le.mpr hdR) (L34MSide.mem_zpowers_of_mem_zpowers hc3 hc1 hd'z hd'1)
  have hcT : c ∈ T := by
    by_contra hcT
    obtain ⟨n, hn⟩ := hfus c hcR hcT
    have hn1 : n * c * n⁻¹ ≠ 1 := by
      intro h
      apply hc1
      have := congrArg (fun v => n⁻¹ * v * n) h
      simpa [mul_assoc] using this
    have hzc : z ∈ Subgroup.zpowers (n * c * n⁻¹) :=
      L34MSide.mem_zpowers_of_mem_zpowers hz3 hz1 hn hn1
    apply hzcomp _ (isComponentOf_map_conj hL₁ n)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzc
    rw [← hk]
    exact ((Commute.zpow_left (L34MSide.central_conj hcc n l hl) k).eq).symm
  have hTnot : ¬ (T : Set Y) ⊆ (Subgroup.zpowers c : Set Y) := by
    intro hsub
    have h1 := Subgroup.card_le_of_le (show T ≤ Subgroup.zpowers c from hsub)
    rw [hT9, Nat.card_zpowers, orderOf_eq_prime hc3 hc1] at h1
    omega
  obtain ⟨s, hsT, hsc⟩ := Set.not_subset.mp hTnot
  have hs1 : s ≠ 1 := fun h => hsc (h ▸ Subgroup.one_mem _)
  set s' := (c * s)⁻¹ with hs'def
  have hs'T : s' ∈ T := T.inv_mem (T.mul_mem hcT hsT)
  have hcs' : s = c⁻¹ * s'⁻¹ := by rw [hs'def, inv_inv]; group
  have hc_s : c = s'⁻¹ * s⁻¹ := by rw [hs'def, inv_inv]; group
  have hs'1 : s' ≠ 1 := by
    intro h
    apply hsc
    rw [hcs', h, inv_one, mul_one]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
  obtain ⟨n₁, hn₁z, hn₁c⟩ := htrz c hcT hc1 s hsT hs1
  obtain ⟨n₂, hn₂z, hn₂c⟩ := htrz c hcT hc1 s' hs'T hs'1
  set L₂ := L₁.map (MulAut.conj n₁).toMonoidHom with hL₂def
  set L₃ := L₁.map (MulAut.conj n₂).toMonoidHom with hL₃def
  have hL₂ : IsComponentOf L₂ ⊤ := isComponentOf_map_conj hL₁ n₁
  have hL₃ : IsComponentOf L₃ ⊤ := isComponentOf_map_conj hL₁ n₂
  set h₂ := n₁ * h₁ * n₁⁻¹ with hh₂def
  set h₃ := n₂ * h₁ * n₂⁻¹ with hh₃def
  have hh₂L : h₂ ∈ L₂ := conj_mem_map_conj n₁ hh₁L
  have hh₃L : h₃ ∈ L₃ := conj_mem_map_conj n₂ hh₁L
  have hsL : s ∈ L₂ := hn₁c ▸ conj_mem_map_conj n₁ hcL
  have hs'L : s' ∈ L₃ := hn₂c ▸ conj_mem_map_conj n₂ hcL
  have hsc₂ : ∀ l ∈ L₂, s * l = l * s := hn₁c ▸ L34MSide.central_conj hcc n₁
  have hs'c₃ : ∀ l ∈ L₃, s' * l = l * s' := hn₂c ▸ L34MSide.central_conj hcc n₂
  have hzh₂ : z * h₂ * z⁻¹ = s * h₂ := by
    have e : z * h₂ * z⁻¹ = n₁ * (z * h₁ * z⁻¹) * n₁⁻¹ := by
      conv_lhs => rw [← hn₁z]
      rw [hh₂def]
      group
    rw [e, hzh₁, ← hn₁c, hh₂def]
    group
  have hzh₃ : z * h₃ * z⁻¹ = s' * h₃ := by
    have e : z * h₃ * z⁻¹ = n₂ * (z * h₁ * z⁻¹) * n₂⁻¹ := by
      conv_lhs => rw [← hn₂z]
      rw [hh₃def]
      group
    rw [e, hzh₁, ← hn₂c, hh₃def]
    group
  have hne12 : L₁ ≠ L₂ := by
    intro h
    apply hsc
    exact (hZ₁ s (h ▸ hsL)).mp (fun l hl => hsc₂ l (h ▸ hl))
  have hne13 : L₁ ≠ L₃ := by
    intro h
    apply hsc
    have hs'z : s' ∈ Subgroup.zpowers c :=
      (hZ₁ s' (h ▸ hs'L)).mp (fun l hl => hs'c₃ l (h ▸ hl))
    rw [hcs']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
      (Subgroup.inv_mem _ hs'z)
  have hne23 : L₂ ≠ L₃ := by
    intro h
    apply hsc
    have hcL₂ : c ∈ L₂ := by
      rw [hc_s]
      exact L₂.mul_mem (L₂.inv_mem (h ▸ hs'L)) (L₂.inv_mem hsL)
    have hcc₂ : ∀ l ∈ L₂, c * l = l * c := by
      intro l hl
      rw [hc_s]
      exact Commute.mul_left (Commute.inv_left (hs'c₃ l (h ▸ hl)))
        (Commute.inv_left (hsc₂ l hl))
    have hcen : ∀ l ∈ L₁, n₁⁻¹ * c * n₁ * l = l * (n₁⁻¹ * c * n₁) :=
      L34MSide.central_of_conj hcc₂
    have hcL₁' : n₁⁻¹ * c * n₁ ∈ L₁ := by
      obtain ⟨c₁, hc₁, hc₁e⟩ := hcL₂
      have e : n₁⁻¹ * c * n₁ = c₁ := by
        rw [← hc₁e]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hc₁
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hZ₁ _ hcL₁').mp hcen)
    have hcs : c ∈ Subgroup.zpowers s := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← hn₁c, conj_zpow, hk]
      group
    have hs3 : s ^ 3 = 1 := by
      rw [← hn₁c, conj_pow, hc3]
      group
    exact L34MSide.mem_zpowers_of_mem_zpowers hs3 hs1 hcs hc1
  have c12 : Commute h₁ h₂ := hcomm_ne hL₂ hL₁ (Ne.symm hne12) hh₁L h₂ hh₂L
  have c13 : Commute h₁ h₃ := hcomm_ne hL₃ hL₁ (Ne.symm hne13) hh₁L h₃ hh₃L
  have c23 : Commute h₂ h₃ := hcomm_ne hL₃ hL₂ (Ne.symm hne23) hh₂L h₃ hh₃L
  set x := h₁ * h₂ * h₃ with hxdef
  have hzx : z * x * z⁻¹ = x := by
    have e : z * x * z⁻¹ = (z * h₁ * z⁻¹) * (z * h₂ * z⁻¹) * (z * h₃ * z⁻¹) := by
      rw [hxdef]
      group
    rw [e, hzh₁, hzh₂, hzh₃]
    have e1 : h₁ * s = s * h₁ := (hcomm_ne hL₁ hL₂ hne12 hsL h₁ hh₁L).symm
    have e2 : h₁ * s' = s' * h₁ := (hcomm_ne hL₁ hL₃ hne13 hs'L h₁ hh₁L).symm
    have e3 : h₂ * s' = s' * h₂ := (hcomm_ne hL₂ hL₃ hne23 hs'L h₂ hh₂L).symm
    calc c * h₁ * (s * h₂) * (s' * h₃) = c * (h₁ * s) * (h₂ * s') * h₃ := by group
      _ = c * (s * h₁) * (s' * h₂) * h₃ := by rw [e1, e3]
      _ = c * s * (h₁ * s') * h₂ * h₃ := by group
      _ = c * s * (s' * h₁) * h₂ * h₃ := by rw [e2]
      _ = (c * s * s') * (h₁ * h₂ * h₃) := by group
      _ = h₁ * h₂ * h₃ := by rw [hs'def]; group
  have hx3 : x ^ 3 = 1 := by
    have hh₂3 : h₂ ^ 3 = 1 := by rw [hh₂def, conj_pow, hh₁3]; group
    have hh₃3 : h₃ ^ 3 = 1 := by rw [hh₃def, conj_pow, hh₁3]; group
    rw [hxdef, (Commute.mul_left c13 c23).mul_pow, c12.mul_pow, hh₁3, hh₂3, hh₃3]
    group
  have hh₁nc : ∃ l ∈ L₁, h₁ * l ≠ l * h₁ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hZ₁ h₁ hh₁L).mp hcon)
    have hzc : z * h₁ * z⁻¹ = h₁ := by
      rw [← hk, show z * c ^ k = c ^ k * z from (Commute.zpow_left hcz k).eq.symm]
      group
    apply hc1
    have e := hzh₁.symm.trans hzc
    calc c = c * h₁ * h₁⁻¹ := by group
      _ = h₁ * h₁⁻¹ := by rw [e]
      _ = 1 := by group
  have hxnc : ∃ l ∈ L₁, x * l ≠ l * x := by
    obtain ⟨l, hl, hne⟩ := hh₁nc
    refine ⟨l, hl, fun h => hne ?_⟩
    have e2 : h₂ * l = l * h₂ := hcomm_ne hL₁ hL₂ hne12 hh₂L l hl
    have e3 : h₃ * l = l * h₃ := hcomm_ne hL₁ hL₃ hne13 hh₃L l hl
    have ex : x * l = h₁ * l * (h₂ * h₃) := by
      rw [hxdef]
      calc h₁ * h₂ * h₃ * l = h₁ * h₂ * (h₃ * l) := by group
        _ = h₁ * h₂ * (l * h₃) := by rw [e3]
        _ = h₁ * (h₂ * l) * h₃ := by group
        _ = h₁ * (l * h₂) * h₃ := by rw [e2]
        _ = h₁ * l * (h₂ * h₃) := by group
    have ex' : l * x = l * h₁ * (h₂ * h₃) := by rw [hxdef]; group
    rw [ex, ex'] at h
    exact mul_right_cancel h
  have hxC : x ∈ Subgroup.centralizer ({z} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * z = (z * x * z⁻¹) * z := by rw [hzx]
      _ = z * x := by group
  obtain ⟨e, -, heR⟩ := hconj x hxC (L34MSide.isPGroup_zpowers_of_pow_three hx3)
  have hE₁ : IsComponentOf (L₁.map (MulAut.conj e⁻¹).toMonoidHom) ⊤ :=
    isComponentOf_map_conj hL₁ e⁻¹
  have hx'nc : ∃ l ∈ L₁.map (MulAut.conj e⁻¹).toMonoidHom,
      e⁻¹ * x * e * l ≠ l * (e⁻¹ * x * e) := by
    have := L34MSide.noncentral_conj hxnc e⁻¹
    simpa only [inv_inv] using this
  have hx'1 : e⁻¹ * x * e ≠ 1 := L34MSide.ne_one_of_noncentral hx'nc
  have hx'T : e⁻¹ * x * e ∉ T := by
    intro hx'T
    obtain ⟨m, hm⟩ := htr c hcT hc1 _ hx'T hx'1
    have hM : IsComponentOf (L₁.map (MulAut.conj m).toMonoidHom) ⊤ :=
      isComponentOf_map_conj hL₁ m
    have hx'M : e⁻¹ * x * e ∈ L₁.map (MulAut.conj m).toMonoidHom :=
      hm ▸ conj_mem_map_conj m hcL
    have hx'cM : ∀ l ∈ L₁.map (MulAut.conj m).toMonoidHom,
        e⁻¹ * x * e * l = l * (e⁻¹ * x * e) :=
      hm ▸ L34MSide.central_conj hcc m
    obtain ⟨l, hl, hne⟩ := hx'nc
    by_cases hME : L₁.map (MulAut.conj m).toMonoidHom = L₁.map (MulAut.conj e⁻¹).toMonoidHom
    · exact hne (hx'cM l (hME ▸ hl))
    · exact hne (hcomm_ne hE₁ hM (Ne.symm hME) hx'M l hl)
  obtain ⟨n, hn⟩ := hfus _ heR hx'T
  have hn1 : n * (e⁻¹ * x * e) * n⁻¹ ≠ 1 := by
    intro h
    apply hx'1
    have := congrArg (fun v => n⁻¹ * v * n) h
    simpa [mul_assoc] using this
  obtain ⟨j, hj⟩ :=
    Subgroup.mem_zpowers_iff.mp (L34MSide.mem_zpowers_of_mem_zpowers hz3 hz1 hn hn1)
  set k := n * e⁻¹ with hkdef
  set a := k * h₁ * k⁻¹ with hadef
  set w := k * (h₂ * h₃) * k⁻¹ with hwdef
  have hnx : n * (e⁻¹ * x * e) * n⁻¹ = a * w := by
    rw [hadef, hwdef, hkdef, hxdef]
    group
  have hK₁ : IsComponentOf (L₁.map (MulAut.conj k).toMonoidHom) ⊤ :=
    isComponentOf_map_conj hL₁ k
  have haK : a ∈ L₁.map (MulAut.conj k).toMonoidHom := conj_mem_map_conj k hh₁L
  have hwK : ∀ l ∈ L₁.map (MulAut.conj k).toMonoidHom, w * l = l * w := by
    have hc23 : ∀ l ∈ L₁, (h₂ * h₃) * l = l * (h₂ * h₃) := by
      intro l hl
      exact Commute.mul_left (hcomm_ne hL₁ hL₂ hne12 hh₂L l hl)
        (hcomm_ne hL₁ hL₃ hne13 hh₃L l hl)
    exact L34MSide.central_conj hc23 k
  have haw : Commute a w := (hwK a haK).symm
  have hz : z = a ^ j * w ^ j := by rw [← hj, hnx, haw.mul_zpow]
  have hyK : a ^ j ∈ L₁.map (MulAut.conj k).toMonoidHom := Subgroup.zpow_mem _ haK j
  have ha3 : a ^ 3 = 1 := by rw [hadef, conj_pow, hh₁3]; group
  have hy3 : (a ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
  have hyz : a ^ j * z = z * a ^ j := by
    have hc : Commute (a ^ j) (w ^ j) := haw.zpow_zpow j j
    rw [hz]
    calc a ^ j * (a ^ j * w ^ j) = a ^ j * (w ^ j * a ^ j) := by rw [hc.eq]
      _ = a ^ j * w ^ j * a ^ j := by group
  have hync : ∃ l ∈ L₁.map (MulAut.conj k).toMonoidHom, a ^ j * l ≠ l * a ^ j := by
    by_contra hcon
    push Not at hcon
    apply hzcomp _ hK₁
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    rw [hz]
    have e1 := hcon l hl
    have e2 : w ^ j * l = l * w ^ j := (Commute.zpow_left (hwK l hl) j).eq
    calc l * (a ^ j * w ^ j) = (l * a ^ j) * w ^ j := by group
      _ = (a ^ j * l) * w ^ j := by rw [e1]
      _ = a ^ j * (l * w ^ j) := by group
      _ = a ^ j * (w ^ j * l) := by rw [e2]
      _ = a ^ j * w ^ j * l := by group
  obtain ⟨l, hl, hne⟩ := hync
  exact hne (hcen _ hK₁ _ hyK (L34MSide.isPGroup_zpowers_of_pow_three hy3) hyz l hl)

end CFSG.AGLEmbedding
