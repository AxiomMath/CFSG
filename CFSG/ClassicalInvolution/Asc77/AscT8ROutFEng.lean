module

public import CFSG.ClassicalInvolution.Asc77.AscT8ROut
public import CFSG.ClassicalInvolution.Asc77.AscT8RAl
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace T8R

open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

section Engine

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T : Subgroup G} {z t : G}

theorem eq_of_mem_conj_sylow_gen (hΩ : HypOmegaGen Ω)
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hJ : J ∈ omegaNbr Ω K)
    (noTwins : ∀ K' ∈ twinSet Ω K, K' = K) (hztc : z * t = t * z) {n : G}
    (hmemn : conjSub n K ∈ Ω) (hJn : conjSub n J ∈ Ω)
    (hzn : IsUniqueInvolution (conjSub n K) (n * z * n⁻¹))
    (htn : IsUniqueInvolution (conjSub n J) (n * t * n⁻¹))
    (hRn : conjSub n R ∈ RSet Ω ∧ conjSub n R ≤ conjSub n K ∧
      conjSub n R ≤ ((conjSylow n S : Sylow 2 G) : Subgroup G))
    (hTn : conjSub n T ∈ RSet Ω ∧ conjSub n T ≤ conjSub n J ∧
      conjSub n T ≤ ((conjSylow n S : Sylow 2 G) : Subgroup G))
    (hcomm : Commutes (conjSub n R) (conjSub n T))
    (hfs : ∀ {s : G}, s ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) →
      (conjSub s (conjSub n R) = conjSub n R ∧ conjSub s (conjSub n T) = conjSub n T) ∨
        (conjSub s (conjSub n R) = conjSub n T ∧ conjSub s (conjSub n T) = conjSub n R))
    (hsw : ∀ {g : G},
      g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) →
        conjSub (g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g) (conjSub n R) = conjSub n T →
          g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g = n * z * n⁻¹ * (n * t * n⁻¹))
    (hc4 : ∀ {g x : G},
      g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) →
        x ∈ conjSub n K → orderOf x = 4 →
          x * (g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g) =
              (g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g) * x →
            g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g = n * z * n⁻¹ * (n * t * n⁻¹))
    (hzO : ∀ {y : G}, y ∈ Subgroup.centralizer ({z} : Set G) →
      ∃ O : Subgroup G, Odd (Nat.card O) ∧ y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ O)
    (htO : ∀ {y : G}, y ∈ Subgroup.centralizer ({t} : Set G) →
      ∃ O : Subgroup G, Odd (Nat.card O) ∧ y * (t * z) * y⁻¹ * (t * z)⁻¹ ∈ O)
    (h93 : ∀ K₀ ∈ Ω, ∀ z₀ : G, IsUniqueInvolution K₀ z₀ →
      ∀ S₀ : Subgroup G, IsSylow2In S₀ (Subgroup.centralizer ({z₀} : Set G)) →
        ∀ U : Subgroup G, U ≤ S₀ → IsElemAbelian2 U 2 → ∀ d ∈ U, d ≠ 1 →
          gamma1 U (S₀ ⊓ ⨆ L ∈ twinSet Ω K₀, L) ≤ Subgroup.centralizer ({d} : Set G) →
            ∃ x ∈ K₀, orderOf x = 4 ∧ x * d = d * x)
    (hzP : z ∈ conjSub n (S : Subgroup G)) (htP : t ∈ conjSub n (S : Subgroup G)) :
    n * (z * t) * n⁻¹ = z * t := by
  by_contra hne
  have hcl := hΩ.conjInvariant
  have hPc : ((conjSylow n S : Sylow 2 G) : Subgroup G) = conjSub n (S : Subgroup G) :=
    coe_conjSylow n S
  have hzP' : z ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) := by rw [hPc]; exact hzP
  have htP' : t ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) := by rw [hPc]; exact htP
  have haP : z * t ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) :=
    (conjSylow n S).mul_mem hzP' htP'
  have hback : n⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * n = z * t := by group
  have hfwd : n * z * n⁻¹ * (n * t * n⁻¹) = n * (z * t) * n⁻¹ := by group
  have hnoswap : conjSub (z * t) (conjSub n R) ≠ conjSub n T := by
    intro h
    have := hsw (g := n) (by rw [hback]; exact haP) (by rw [hback]; exact h)
    rw [hback, hfwd] at this
    exact hne this.symm
  have hno4 : ¬ ∃ x ∈ conjSub n K, orderOf x = 4 ∧ x * (z * t) = (z * t) * x := by
    rintro ⟨x, hxK, hx4, hxc⟩
    have := hc4 (g := n) (by rw [hback]; exact haP) hxK hx4
      (by rw [hback]; exact hxc)
    rw [hback, hfwd] at this
    exact hne this.symm
  have hz2 : z * z = 1 := hz.sq
  have ht2 : t * t = 1 := ht.sq
  have hz1 : z ≠ 1 := hz.ne_one
  have ht1 : t ≠ 1 := ht.ne_one
  have hzt : z ≠ t := by
    intro h'
    exact hJ.2.1 (noTwins J ⟨hJ.1, z, hz, h' ▸ ht⟩)
  have hK'Ω : conjSub n K ∈ Ω := hmemn
  obtain ⟨hR'Ω, hR'K', hR'P⟩ := hRn
  obtain ⟨hT'Ω, hT'J', hT'P⟩ := hTn
  have hR'syl : IsSylow2In (conjSub n R) (conjSub n K) :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hR'Ω hR'K'
  have hT'syl : IsSylow2In (conjSub n T) (conjSub n J) :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJn hT'Ω hT'J'
  have h8R := Sec6Gen.eight_le_of_mem_RSet hΩ hR'Ω
  have h8T := Sec6Gen.eight_le_of_mem_RSet hΩ hT'Ω
  have hz'R : n * z * n⁻¹ ∈ conjSub n R :=
    T3.mem_of_isPGroup hzn hR'K' hR'syl.2.1 (by omega)
  have hz'Ru : IsUniqueInvolution (conjSub n R) (n * z * n⁻¹) :=
    uniqueInvolution_restrict hzn hR'K' hz'R
  have ht'T : n * t * n⁻¹ ∈ conjSub n T :=
    T3.mem_of_isPGroup htn hT'J' hT'syl.2.1 (by omega)
  have ht'Tu : IsUniqueInvolution (conjSub n T) (n * t * n⁻¹) :=
    uniqueInvolution_restrict htn hT'J' ht'T
  have hz't' : n * z * n⁻¹ ≠ n * t * n⁻¹ := by
    intro h
    apply hzt
    have h' : n⁻¹ * (n * z * n⁻¹) * n = n⁻¹ * (n * t * n⁻¹) * n := by rw [h]
    simpa [mul_assoc] using h'
  have hPpg : IsPGroup 2 ↥(conjSylow n S : Sylow 2 G) := (conjSylow n S).isPGroup'
  rcases hfs hzP' with ⟨hzR, hzT⟩ | ⟨hzR, hzT⟩ <;>
    rcases hfs htP' with ⟨htR, htT⟩ | ⟨htR, htT⟩
  ·
    have hR'2 : IsPGroup 2 ↥(conjSub n R) := hR'syl.2.1
    have hzK' : conjSub z (conjSub n K) = conjSub n K :=
      Sec6Gen.eq_of_le_of_le hΩ (hcl z _ hK'Ω) hK'Ω hR'2 (by omega) (hzR ▸ conjSub_mono hR'K') hR'K'
    have htK' : conjSub t (conjSub n K) = conjSub n K :=
      Sec6Gen.eq_of_le_of_le hΩ (hcl t _ hK'Ω) hK'Ω hR'2 (by omega) (htR ▸ conjSub_mono hR'K') hR'K'
    have hzc : z * (n * z * n⁻¹) = (n * z * n⁻¹) * z := by
      have h : IsUniqueInvolution (conjSub n K) (z * (n * z * n⁻¹) * z⁻¹) := by
        have := hzn.conj z
        rwa [hzK'] at this
      have h' := hzn.eq h
      calc z * (n * z * n⁻¹) = (z * (n * z * n⁻¹) * z⁻¹) * z := by group
        _ = (n * z * n⁻¹) * z := by rw [← h']
    have htc : t * (n * z * n⁻¹) = (n * z * n⁻¹) * t := by
      have h : IsUniqueInvolution (conjSub n K) (t * (n * z * n⁻¹) * t⁻¹) := by
        have := hzn.conj t
        rwa [htK'] at this
      have h' := hzn.eq h
      calc t * (n * z * n⁻¹) = (t * (n * z * n⁻¹) * t⁻¹) * t := by group
        _ = (n * z * n⁻¹) * t := by rw [← h']
    obtain ⟨U, hUel, hzU, htU, hUenum⟩ := exists_fourGroup hz2 ht2 hz1 ht1 hzt hztc
    have hUle : U ≤ Subgroup.centralizer ({n * z * n⁻¹} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hUenum y hy with h | h | h | h
      · rw [h]
        simp
      · rw [h]
        exact hzc
      · rw [h]
        exact htc
      · rw [h]
        exact Commute.mul_left (a := z) (b := t) (c := n * z * n⁻¹) hzc htc
    have hU2 : IsPGroup 2 ↥U := IsPGroup.of_card (n := 2) hUel.1
    obtain ⟨S'', hS''syl, hUS''⟩ := IsSylow2In.exists_ge hU2 hUle
    have hS''2 : IsPGroup 2 ↥S'' := hS''syl.2.1
    have haU : z * t ∈ U := U.mul_mem hzU htU
    have haS'' : z * t ∈ S'' := hUS'' haU
    have ha1 : z * t ≠ 1 := by
      intro h
      have h' : z = t⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [inv_eq_of_mul_eq_one_right ht2] at h'
      exact hzt h'
    have hu : ∀ y' : G, y' ∈ S'' → y' * (z * t) * y'⁻¹ ∈ S'' := fun y' hy' =>
      S''.mul_mem (S''.mul_mem hy' haS'') (S''.inv_mem hy')
    have hΓ : gamma1 U (S'' ⊓ ⨆ L ∈ twinSet Ω (conjSub n K), L) ≤
        Subgroup.centralizer ({z * t} : Set G) := by
      refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
      intro y hy
      have hyS : y ∈ S'' := hy.1.1
      have hyw : y ∈ Subgroup.centralizer ({w} : Set G) := hy.2
      rw [Subgroup.mem_centralizer_singleton_iff] at hyw
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hUenum w hw with h | h | h | h
      · exact (hw1 h).elim
      · rw [h] at hyw
        have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hyw
        obtain ⟨O₁, hO₁, h1⟩ := hzO hyC
        have h2 := eq_of_mul_inv_mem_odd hS''2 (hu y hyS) haS'' hO₁ h1
        calc y * (z * t) = (y * (z * t) * y⁻¹) * y := by group
          _ = (z * t) * y := by rw [h2]
      · rw [h] at hyw
        have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hyw
        obtain ⟨O₂, hO₂, h1⟩ := htO hyC
        rw [← hztc] at h1
        have h2 := eq_of_mul_inv_mem_odd hS''2 (hu y hyS) haS'' hO₂ h1
        calc y * (z * t) = (y * (z * t) * y⁻¹) * y := by group
          _ = (z * t) * y := by rw [h2]
      · rw [h] at hyw
        exact hyw
    obtain ⟨x, hxK, hx4, hxc⟩ := h93 (conjSub n K) hK'Ω (n * z * n⁻¹) hzn S'' hS''syl U hUS'' hUel
      (z * t) haU ha1 hΓ
    exact hno4 ⟨x, hxK, hx4, hxc⟩
  · exact hnoswap (by rw [conjSub_mul, htR, hzT])
  · exact hnoswap (by rw [conjSub_mul, htR, hzR])
  ·
    have haR : conjSub (z * t) (conjSub n R) = conjSub n R := by rw [conjSub_mul, htR, hzT]
    obtain ⟨r, hrR, hr4⟩ := exists_orderOf_four_of_four_le hzn hR'K' hR'syl.2.1 (by omega)
    obtain ⟨s, hsdef⟩ : ∃ s : G, s = z * r * z⁻¹ := ⟨_, rfl⟩
    obtain ⟨r₂, hr₂def⟩ : ∃ r₂ : G, r₂ = (z * t) * r * (z * t)⁻¹ := ⟨_, rfl⟩
    obtain ⟨s₂, hs₂def⟩ : ∃ s₂ : G, s₂ = z * r₂ * z⁻¹ := ⟨_, rfl⟩
    have hr₂R : r₂ ∈ conjSub n R := by
      have := conj_mem_conjSub (n := z * t) hrR
      rw [haR] at this
      rw [hr₂def]
      exact this
    have hsT : s ∈ conjSub n T := by
      have := conj_mem_conjSub (n := z) hrR
      rw [hzR] at this
      rw [hsdef]
      exact this
    have hs₂T : s₂ ∈ conjSub n T := by
      have := conj_mem_conjSub (n := z) hr₂R
      rw [hzR] at this
      rw [hs₂def]
      exact this
    have hyz : z * (r * s) = (r * s) * z := by
      have h1 : z * s * z⁻¹ = r := by
        calc z * s * z⁻¹ = (z * z) * r * (z * z)⁻¹ := by rw [hsdef]; group
          _ = r := by rw [hz2]; group
      have h2 : s * r = r * s := (hcomm r hrR s hsT).symm
      calc z * (r * s) = (z * r * z⁻¹) * (z * s * z⁻¹) * z := by group
        _ = s * r * z := by rw [h1, ← hsdef]
        _ = (r * s) * z := by rw [h2]
    have hyP : r * s ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) :=
      (conjSylow n S).mul_mem (hR'P hrR) (hT'P hsT)
    have hyC : r * s ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyz.symm
    obtain ⟨O₃, hO₃, h1⟩ := hzO hyC
    have h2 : r * s * (z * t) * (r * s)⁻¹ = z * t :=
      eq_of_mul_inv_mem_odd hPpg
        ((conjSylow n S).mul_mem ((conjSylow n S).mul_mem hyP haP) ((conjSylow n S).inv_mem hyP))
        haP hO₃ h1
    have hya : (r * s) * (z * t) = (z * t) * (r * s) := by
      calc (r * s) * (z * t) = ((r * s) * (z * t) * (r * s)⁻¹) * (r * s) := by group
        _ = (z * t) * (r * s) := by rw [h2]
    have haz : (z * t) * z = z * (z * t) := by
      calc (z * t) * z = z * (t * z) := by rw [mul_assoc]
        _ = z * (z * t) := by rw [← hztc]
    have haza : (z * t) * z * (z * t)⁻¹ = z := by rw [haz]; group
    have hs₂ : (z * t) * s * (z * t)⁻¹ = s₂ := by
      rw [hsdef, hs₂def, hr₂def]
      calc (z * t) * (z * r * z⁻¹) * (z * t)⁻¹
          = ((z * t) * z * (z * t)⁻¹) * ((z * t) * r * (z * t)⁻¹) *
            ((z * t) * z * (z * t)⁻¹)⁻¹ := by group
        _ = z * ((z * t) * r * (z * t)⁻¹) * z⁻¹ := by rw [haza]
    have hprod : r₂ * s₂ = r * s := by
      calc r₂ * s₂ = ((z * t) * r * (z * t)⁻¹) * ((z * t) * s * (z * t)⁻¹) := by
            rw [hs₂, hr₂def]
        _ = (z * t) * (r * s) * (z * t)⁻¹ := by group
        _ = r * s := by rw [← hya]; group
    have hrr : r⁻¹ * r₂ = s * s₂⁻¹ := by
      calc r⁻¹ * r₂ = r⁻¹ * (r₂ * s₂) * s₂⁻¹ := by group
        _ = r⁻¹ * (r * s) * s₂⁻¹ := by rw [hprod]
        _ = s * s₂⁻¹ := by group
    have hrr1 : r⁻¹ * r₂ = 1 :=
      eq_one_of_mem_inf hz'Ru ht'Tu hz't' hR'syl.2.1
        ((conjSub n R).mul_mem ((conjSub n R).inv_mem hrR) hr₂R)
        (by rw [hrr]; exact (conjSub n T).mul_mem hsT ((conjSub n T).inv_mem hs₂T))
    have hr₂r : r₂ = r := (inv_mul_eq_one.mp hrr1).symm
    have h3 : (z * t) * r * (z * t)⁻¹ = r := hr₂def.symm.trans hr₂r
    have hxc : r * (z * t) = (z * t) * r := by
      calc r * (z * t) = ((z * t) * r * (z * t)⁻¹) * (z * t) := by rw [h3]
        _ = (z * t) * r := by group
    exact hno4 ⟨r, hR'K' hrR, hr4, hxc⟩

end Engine

end T8R

end CFSG.ClassicalInvolution.Asc77
