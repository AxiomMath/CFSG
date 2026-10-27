module

public import CFSG.GH74.Generic.FrameSylow
public import CFSG.Adapters.Involutions

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup

variable {G : Type} [Group G]

@[expose] def barOf {x : G} {u : G} (hu : u ∈ centralizer ({x} : Set G)) : CentralizerBar x :=
  QuotientGroup.mk (⟨u, hu⟩ : ↥(centralizer ({x} : Set G)))

@[expose] def NoNoncentralInvolutionConj (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ (u : G) (hu : u ∈ centralizer ({x} : Set G)), u * u = 1 → barOf hu ∈ K → barOf hu ≠ xbar x →
    ¬ IsConj x u

variable [Finite G]

theorem exists_conj_in_sylow_ne (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {x : G}
    (hx : orderOf x = 2) (T : Sylow 2 G) (hxT : x ∈ (T : Subgroup G))
    (hxc : ∀ t ∈ (T : Subgroup G), t * x = x * t) :
    ∃ g : G, g⁻¹ * x * g ∈ (T : Subgroup G) ∧ g⁻¹ * x * g ≠ x := by
  by_contra hcon
  push Not at hcon
  have hzZ : (⟨x, hxT⟩ : ↥(T : Subgroup G)) ∈ Subgroup.center ↥(T : Subgroup G) :=
    Subgroup.mem_center_iff.2 fun t => Subtype.ext (hxc t t.2)
  have hord : orderOf (⟨x, hxT⟩ : ↥(T : Subgroup G)) = 2 :=
    (Subgroup.orderOf_mk x hxT).trans hx
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar T ⟨x, hxT⟩ hzZ hord (fun g hg => hcon g hg)
  have hbot : oddCore G = ⊥ := by
    rcases (inferInstance : (oddCore G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hx (h ▸ Subgroup.mem_top x)
  have hxcen : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.1 hcen (QuotientGroup.mk g)
    have h2 : (QuotientGroup.mk (g * x) : G ⧸ oddCore G) = QuotientGroup.mk (x * g) := h1
    have h3 := (QuotientGroup.eq).1 h2
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact h3
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.mem_bot] at hxcen
    rw [hxcen, orderOf_one] at hx
    omega
  · obtain ⟨a, b, hab⟩ := hn
    exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a)

theorem exists_outer_involution (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hG : Gen4 G) {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)}
    (hfr : Q8Frame ↥K) (hB5 : NoNoncentralInvolutionConj x K) :
    ∃ (v : G) (hv : v ∈ centralizer ({x} : Set G)), IsConj x v ∧ v ≠ x ∧ v * v = 1 ∧
      barOf hv ≠ 1 ∧ barOf hv ≠ xbar x ∧ barOf hv ∉ K := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) := inferInstance
  obtain ⟨T, hTS, hxT, hxc, -⟩ := frame_sylow_centralizer_isSylow hG hx hfr S
  obtain ⟨g, hgT, hgne⟩ := exists_conj_in_sylow_ne hs hn hx T hxT hxc
  set v : G := g⁻¹ * x * g with hvdef
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hvv : v * v = 1 := by
    calc v * v = g⁻¹ * (x * x) * g := by rw [hvdef]; group
      _ = 1 := by rw [hxx]; group
  have hvC : v ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hxc v hgT)
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hv1 : v ≠ 1 := by
    intro h
    apply hx1
    have : x = g * v * g⁻¹ := by simp [v, mul_assoc]
    rw [this, h]
    simp
  have hconj : IsConj x v := isConj_iff.2 ⟨g⁻¹, by simp [v, mul_assoc]⟩
  rw [hTS] at hgT
  obtain ⟨s, hsS, hsv⟩ := hgT
  have hsv' : s = ⟨v, hvC⟩ := Subtype.ext hsv
  refine ⟨v, hvC, hconj, fun h => hgne h, hvv, ?_, ?_, ?_⟩
  ·
    intro h1
    have hmem := (QuotientGroup.eq_one_iff _).1 h1
    have hs1 : s ∈ pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set G)) := by
      rw [hsv']; exact hmem
    have := eq_one_of_mem_sylow_of_mem_pPrimeCore S hsS hs1
    apply hv1
    rw [← hsv, this]
    rfl
  ·
    intro h1
    have hmem : (xH x)⁻¹ * s ∈ pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set G)) := by
      rw [hsv']
      exact (QuotientGroup.eq).1 h1.symm
    have hS' : (xH x)⁻¹ * s ∈ (S : Subgroup _) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (xH_mem_sylow hx S)) hsS
    have := eq_one_of_mem_sylow_of_mem_pPrimeCore S hS' hmem
    have hsx : s = xH x := by
      rw [inv_mul_eq_one] at this
      exact this.symm
    apply hgne
    have : (s : G) = x := by rw [hsx]; rfl
    rw [← this]
    exact hsv.symm
  · intro hK
    exact hB5 v hvC hvv hK (fun h => hgne (by
      have hmem : (xH x)⁻¹ * s ∈ pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set G)) := by
        rw [hsv']
        exact (QuotientGroup.eq).1 h.symm
      have hS' : (xH x)⁻¹ * s ∈ (S : Subgroup _) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (xH_mem_sylow hx S)) hsS
      have h0 := eq_one_of_mem_sylow_of_mem_pPrimeCore S hS' hmem
      have hsx : s = xH x := by
        rw [inv_mul_eq_one] at h0
        exact h0.symm
      have : (s : G) = x := by rw [hsx]; rfl
      rw [← this]
      exact hsv.symm)) hconj

end CFSG.GH74.Generic
