module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6AutOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6E27
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Datum
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Endgame
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

section Aux

variable {G : Type*} [Group G]

theorem conj_mem_centralizer_of_mem_normalizer {K : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hc : c ∈ Subgroup.centralizer (K : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
    simpa using this
  have hcomm : g⁻¹ * k * g * c = c * (g⁻¹ * k * g) := Subgroup.mem_centralizer_iff.mp hc _ hk'
  calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [hcomm]
    _ = g * c * g⁻¹ * k := by group

theorem pCoreOf_conj_mem {C : Subgroup G} [Finite G] {g : G} (hg : ∀ x ∈ C, g * x * g⁻¹ ∈ C)
    (hg' : ∀ x ∈ C, g⁻¹ * x * g ∈ C) {r : G} (hr : r ∈ pCoreOf 2 C) :
    g * r * g⁻¹ ∈ pCoreOf 2 C := by
  have hmap : C.map (MulAut.conj g).toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hg y hy
    · intro hx
      refine ⟨g⁻¹ * x * g, hg' x hx, ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  have := pCoreOf_map_equiv 2 (MulAut.conj g) C
  rw [hmap] at this
  rw [this]
  exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩

end Aux

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs}

theorem A6Datum.centralizer_t_le_H {t zK : G} (D : A6Datum N) (h : Lv2521 N t zK) :
    Subgroup.centralizer ({t} : Set G) ≤ N.H := by
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  have hf := h.facts2511
  have h254 := h.facts254
  have h258 := h.facts258
  have hsimple := h258.simple
  have hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  obtain ⟨-, hGteq, -, hCchar, -⟩ := h.concl2518
  rw [hK0] at hGteq hCchar
  set Gt : Subgroup G := Subgroup.centralizer ({t} : Set G) with hGt
  set C : Subgroup G := Gt ⊓ Subgroup.centralizer (N.K : Set G) with hC
  have hKGt : N.K ≤ Gt := fun k hk => hf.H_le (N.K_le_H hk)
  have hSGt : N.S ≤ Gt := hf.sylow.le
  have hCGt : C ≤ Gt := inf_le_left
  have hCcent : C ≤ Subgroup.centralizer (N.K : Set G) := inf_le_right
  have hGtN : Gt ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [hGteq]
    refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
    · exact fun s hs' => hKH (N.S_le_H hs')
    · exact hCcent.trans (Subgroup.centralizer_le_normalizer _)
  have hCnorm : ∀ g ∈ Gt, ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g hg c hc =>
    ⟨Gt.mul_mem (Gt.mul_mem hg (hCGt hc)) (Gt.inv_mem hg),
      conj_mem_centralizer_of_mem_normalizer (hGtN hg) (hCcent hc)⟩
  have hCnorm' : ∀ g ∈ Gt, ∀ c ∈ C, g⁻¹ * c * g ∈ C := fun g hg c hc => by
    have := hCnorm g⁻¹ (Gt.inv_mem hg) c hc
    simpa using this
  have hGtNC : Gt ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hCnorm g hg c
    · intro hc
      have := hCnorm' g hg _ hc
      simpa [mul_assoc] using this
  suffices hC2 : IsPGroup 2 C by
    have hCS : C ≤ N.S := hf.sylow.le_of_normalizes hCGt hGtNC hC2
    rw [hGteq]
    exact sup_le (sup_le (fun k hk => N.K_le_H hk) (fun s hs' => N.S_le_H hs'))
      (fun c hc => N.S_le_H (hCS hc))
  have hCS2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := pCoreOf 2 C with hR
  have hR2 : IsPGroup 2 R := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 C
  have hRC : R ≤ C := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 C
  have hRnorm : ∀ g ∈ Gt, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
    pCoreOf_conj_mem (hCnorm g hg) (hCnorm' g hg) hr
  have hRnorm' : ∀ g ∈ Gt, ∀ r ∈ R, g⁻¹ * r * g ∈ R := fun g hg r hr => by
    have := hRnorm g⁻¹ (Gt.inv_mem hg) r hr
    simpa using this
  have hGtNR : Gt ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · exact hRnorm g hg r
    · intro hr
      have := hRnorm' g hg _ hr
      simpa [mul_assoc] using this
  have hRS : R ≤ N.S := hf.sylow.le_of_normalizes (hRC.trans hCGt) hGtNR hR2
  have hRSC : R ≤ N.SC := by
    refine fun r hr => ⟨hRS hr, ?_⟩
    rw [hK0]
    exact hCcent (hRC hr)
  apply IsPGroup.of_card (n := (Nat.card C).primeFactorsList.length)
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro prime hprime hdvd
  by_contra hne2
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨c0, hc0⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) prime hdvd
  set c : G := (c0 : G) with hcdef
  have hcC : c ∈ C := c0.2
  have hcord : orderOf c = prime := by rw [hcdef, Subgroup.orderOf_coe]; exact hc0
  have hcpow : c ^ prime = 1 := by rw [← hcord]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hcord
    exact hprime.one_lt.ne hcord
  have hcGt : c ∈ Gt := hCGt hcC
  have hcK : ∀ k ∈ N.K, c * k = k * c := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hCcent hcC) k hk).symm
  have hnotcent : ¬ ∀ r ∈ R, c * r = r * c := by
    intro hall
    have hcR : c ∈ R := by
      have hmem : c ∈ C ⊓ Subgroup.centralizer (pCoreOf 2 C : Set G) := by
        exact ⟨hcC, Subgroup.mem_centralizer_iff.mpr (fun r hr => (hall r hr).symm)⟩
      exact hCchar hmem
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR2 ⟨c, hcR⟩
    have hk' : orderOf c = 2 ^ k := (Subgroup.orderOf_coe (⟨c, hcR⟩ : R)).trans hk
    rw [hcord] at hk'
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero] at hk'
      exact hprime.one_lt.ne' hk'
    · have h2dvd : 2 ∣ prime := by rw [hk']; exact dvd_pow_self 2 hk0.ne'
      exact hne2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h2dvd).symm
  have hprime3 : prime = 3 ∨ 5 ≤ prime := by
    have h2 := hprime.two_le
    have h4 : prime ≠ 4 := by
      rintro rfl
      exact absurd hprime (by decide)
    omega
  rcases hprime3 with h3 | h5
  ·
    subst h3
    obtain ⟨eK⟩ := h.concl2521.nonempty_K
    obtain ⟨E, hEle, hE, hcard⟩ := exists_elemAbelian_27 eK hZ hcpow hc1 hcK
    have hEGt : E ≤ Gt := hEle.trans (sup_le hKGt (Subgroup.zpowers_le.mpr hcGt))
    have ht2 : t * t = 1 := hf.t_mul_t
    have htpow2 : IsPGroup 2 ↥(Subgroup.zpowers t) :=
      N.tuple.sylow.isPGroup.to_le (Subgroup.zpowers_le.mpr hf.t_mem_center.1)
    have hGtN2 : Gt ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
      rw [hGt, ← normalizer_zpowers_eq_centralizer ht2]
    have hzt : Subgroup.zpowers t ≤ Gt := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hO2 : pCoreOf 2 Gt ≠ ⊥ := by
      intro hbot
      have := le_pCoreOf_of_le_normalizer hzt hGtN2 htpow2
      rw [hbot] at this
      exact hf.t_ne_one (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp this))
    exact Unc25G2.false_of_isElemAbelian_card_cube hs.setting.qtke.2.2 hO2 hEGt (by norm_num)
      (by norm_num) hE hcard
  ·
    have hxS : ∀ s ∈ N.S, N.x * s * N.x⁻¹ ∈ N.S := fun s hs' =>
      (Subgroup.mem_normalizer_iff.mp N.x_mem.2 s).mp hs'
    have hxS' : ∀ s ∈ N.S, N.x⁻¹ * s * N.x ∈ N.S := fun s hs' => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ N.x_mem.2) s).mp hs'
      simpa using this
    let ι : ↥R →* P10 :=
      { toFun := fun r => D.Φ (N.x * (r : G) * N.x⁻¹)
        map_one' := by simpa using D.Φ_one
        map_mul' := fun a b => by
          have e : N.x * ((a * b : ↥R) : G) * N.x⁻¹ =
              (N.x * (a : G) * N.x⁻¹) * (N.x * (b : G) * N.x⁻¹) := by
            simp only [Subgroup.coe_mul]; group
          simp only [e]
          exact D.mul _ (N.S_le_H (hxS _ (hRS a.2))) _ (N.S_le_H (hxS _ (hRS b.2))) }
    have hinj : Function.Injective ι := by
      intro a b hab
      have hxa := hxS _ (hRS a.2)
      have hxb := hxS _ (hRS b.2)
      have h1 := D.inv_mul_mem_SC hK0 hxa hxb hab
      have hmem : (a : G)⁻¹ * b ∈ CFSG.conjugate N.SC N.x := by
        rw [mem_conjugate_iff]
        have e : N.x * ((a : G)⁻¹ * b) * N.x⁻¹ =
            (N.x * (a : G) * N.x⁻¹)⁻¹ * (N.x * (b : G) * N.x⁻¹) := by group
        rw [e]
        exact h1
      have hSCm : (a : G)⁻¹ * b ∈ N.SC := hRSC (R.mul_mem (R.inv_mem a.2) b.2)
      have h3 : (a : G)⁻¹ * b ∈ N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨hSCm, hmem⟩
      rw [h.concl255.1, Subgroup.mem_bot] at h3
      exact Subtype.ext (inv_mul_eq_one.mp h3)
    have hP : ∀ r : ↥R, ι r ∈ P0 := fun r => D.S_mem _ (hxS _ (hRS r.2))
    have hnormP : ∀ g ∈ P0, ∀ r : ↥R, ∃ r' : ↥R, ι r' = g * ι r * g⁻¹ := by
      intro g hg r
      obtain ⟨s, hsS, rfl⟩ := D.S_surj g hg
      have hs'S := hxS' s hsS
      have hr' : N.x⁻¹ * s * N.x * (r : G) * (N.x⁻¹ * s * N.x)⁻¹ ∈ R :=
        hRnorm _ (hSGt hs'S) _ r.2
      refine ⟨⟨_, hr'⟩, ?_⟩
      show D.Φ (N.x * (N.x⁻¹ * s * N.x * (r : G) * (N.x⁻¹ * s * N.x)⁻¹) * N.x⁻¹) = _
      have e : N.x * (N.x⁻¹ * s * N.x * (r : G) * (N.x⁻¹ * s * N.x)⁻¹) * N.x⁻¹ =
          s * (N.x * (r : G) * N.x⁻¹) * s⁻¹ := by group
      rw [e]
      exact D.Φ_conj (N.S_le_H hsS) (N.S_le_H (hxS _ (hRS r.2)))
    let α : ↥R ≃* ↥R :=
      { toFun := fun r => ⟨c * (r : G) * c⁻¹, hRnorm c hcGt r r.2⟩
        invFun := fun r => ⟨c⁻¹ * (r : G) * c, hRnorm' c hcGt r r.2⟩
        left_inv := fun r => Subtype.ext (by
          show c⁻¹ * (c * (r : G) * c⁻¹) * c = r
          group)
        right_inv := fun r => Subtype.ext (by
          show c * (c⁻¹ * (r : G) * c) * c⁻¹ = r
          group)
        map_mul' := fun a b => Subtype.ext (by
          show c * ((a : G) * b) * c⁻¹ = (c * (a : G) * c⁻¹) * (c * (b : G) * c⁻¹)
          group) }
    have hiter : ∀ (n : ℕ) (r : ↥R), (((⇑α)^[n] r : ↥R) : G) = c ^ n * (r : G) * (c ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro r; simp
      | succ n ih =>
        intro r
        rw [Function.iterate_succ_apply, ih]
        show c ^ n * (c * (r : G) * c⁻¹) * (c ^ n)⁻¹ = c ^ (n + 1) * (r : G) * (c ^ (n + 1))⁻¹
        rw [pow_succ]
        group
    have hα : ∀ r : ↥R, (⇑α)^[prime] r = r := by
      intro r
      apply Subtype.ext
      rw [hiter, hcpow]
      simp
    have hne : ∃ r : ↥R, α r ≠ r := by
      by_contra hcon
      push Not at hcon
      apply hnotcent
      intro r hr
      have h1 : c * r * c⁻¹ = r := congrArg Subtype.val (hcon ⟨r, hr⟩)
      calc c * r = (c * r * c⁻¹) * c := by group
        _ = r * c := by rw [h1]
    exact no_odd_prime_aut_of_normal ι hinj hP hnormP α hprime h5 hα hne

end Main

end CFSG.QuasithinUnique
