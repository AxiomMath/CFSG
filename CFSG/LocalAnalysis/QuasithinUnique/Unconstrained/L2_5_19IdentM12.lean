module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.QuasithinUnique.Id2519.Tab

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem card_fixSub_transAut {K : Type} {N : Type*} [Group K] [Group N] (ψ : K ≃* N) (β : K ≃* K) :
    Nat.card (fixSub (transAut ψ β)) = Nat.card (fixSub β) := by
  have h : (fixSub β).map ψ.toMonoidHom = fixSub (transAut ψ β) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_fixSub]
      change transAut ψ β (ψ x) = ψ x
      rw [transAut_apply, (mem_fixSub.mp hx)]
    · intro hy
      obtain ⟨x, rfl⟩ := ψ.surjective y
      refine ⟨x, ?_, rfl⟩
      show x ∈ fixSub β
      rw [mem_fixSub]
      have h1 := (mem_fixSub.mp hy)
      change transAut ψ β (ψ x) = ψ x at h1
      rw [transAut_apply] at h1
      exact ψ.injective h1
  rw [← h, Subgroup.card_map_of_injective ψ.injective]

theorem card_centralizer_involution_M12
    {p : NativeSporadic.M12} (hp : orderOf p = 2) :
    Nat.card (Subgroup.centralizer ({p} : Set NativeSporadic.M12)) = 192 ∨
      Nat.card (Subgroup.centralizer ({p} : Set NativeSporadic.M12)) = 240 := by
  have hp' : orderOf (p : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hp
  obtain ⟨r, hr, c, hcM, hpc⟩ := m12_involution_cover.1 (p : Equiv.Perm (Fin 12)) (by simp) hp'
  have hmap : (Subgroup.centralizer ({p} : Set NativeSporadic.M12)).map
      NativeSporadic.M12.subtype = centralizerIn NativeSporadic.M12 (p : Equiv.Perm (Fin 12)) := by
    ext x
    rw [mem_centralizerIn]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hxp), rfl⟩
  have hcard : Nat.card (Subgroup.centralizer ({p} : Set NativeSporadic.M12)) =
      Nat.card (centralizerIn NativeSporadic.M12 (p : Equiv.Perm (Fin 12))) := by
    rw [← hmap, Subgroup.card_map_of_injective NativeSporadic.M12.subtype_injective]
  rw [hcard, hpc, centralizerIn_conj NativeSporadic.M12 hcM,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    exact card_centralizerIn_m12Rep1
  · right
    exact card_centralizerIn_m12Rep2

section Main

variable {G : Type} [Group G] [Finite G]

theorem tabIdentFor_m12
    : TabIdentFor (@Ident.FamSporadic .M12) := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨e0⟩ := hX
  have hZ : Subgroup.center ↥X = CFSG.pCore 2 ↥X := hs.center_eq_pCore e0 m12_center_eq_bot'
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.M12 :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans e0
  have hπ := quotProj_surjective e'
  have hker := quotProj_ker e'
  set α := quotAct (quotProj e') hπ hker hs.tN with hαdef
  have hα2 : α * α = 1 := quotAct_mul_self (quotProj e') hπ hker hs.tN hs.sq
  have hα1 : α ≠ 1 := quotAct_ne_one (quotProj e') hπ hker hs.tN hs.quasi hs.comm
  let ρ : ↥K →* NativeSporadic.M12 := (quotProj e').comp (Subgroup.inclusion hs.K_le)
  have hρinj : Function.Injective ρ := hs.injective_proj hs.ktype (quotProj e') hker
  have hKcard : Nat.card ρ.range = Nat.card ↥K :=
    (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hKfix : ρ.range ≤ fixSub α := by
    rintro _ ⟨k, rfl⟩
    rw [mem_fixSub]
    have hkt : (k : G) * t = t * (k : G) := Subgroup.mem_centralizer_singleton_iff.mp
      (hs.K_le_cent k.2)
    have hy : ((Subgroup.inclusion hs.K_le k : X) : G) =
        t * ((Subgroup.inclusion hs.K_le k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply (quotProj e') hπ hker hs.tN _ _ hy
  have hdvd : Nat.card ↥K ∣ Nat.card (fixSub α) := by
    rw [← hKcard]
    exact Subgroup.card_dvd_of_le hKfix
  have hle := Nat.le_of_dvd Nat.card_pos hdvd
  have hF : Nat.card (fixSub α) = 120 ∨ Nat.card (fixSub α) = 192 ∨
      Nat.card (fixSub α) = 240 := by
    by_cases hin : α ∈ OuterAutomorphisms.inner NativeSporadic.M12
    · obtain ⟨p, hp⟩ := hin
      have hp2 : p * p = 1 := by
        have h1 : MulAut.conj (p * p) = 1 := by rw [map_mul, hp, hα2]
        have h2 : p * p ∈ Subgroup.center NativeSporadic.M12 := by
          rw [Subgroup.mem_center_iff]
          intro q
          have h3 := congrArg (fun σ : MulAut NativeSporadic.M12 => σ q) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at h3
          calc q * (p * p) = (p * p * q * (p * p)⁻¹) * (p * p) := by rw [h3]
            _ = p * p * q := by group
        rw [m12_center_eq_bot', Subgroup.mem_bot] at h2
        exact h2
      have hp1 : p ≠ 1 := by
        rintro rfl
        apply hα1
        rw [← hp, map_one]
      have hpo : orderOf p = 2 := orderOf_eq_prime (by rw [sq]; exact hp2) hp1
      have hfix : fixSub α = Subgroup.centralizer ({p} : Set NativeSporadic.M12) := by
        ext q
        rw [mem_fixSub, ← hp, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
        constructor
        · intro h
          calc q * p = (p * q * p⁻¹) * p := by rw [h]
            _ = p * q := by group
        · intro h
          calc p * q * p⁻¹ = (q * p) * p⁻¹ := by rw [h]
            _ = q := by group
      rw [hfix]
      rcases card_centralizer_involution_M12 hpo with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · left
      have hαinv : ∀ x, α (α x) = x := fun x => by
        have := congrArg (fun σ : MulAut NativeSporadic.M12 => σ x) hα2
        simpa using this
      have hout : transAut m12EquivD α ∉ OuterAutomorphisms.inner m12D.originalSubgroup := by
        intro h
        obtain ⟨l, hl⟩ := isInnerAut_of_transAut_mem_inner m12EquivD α h
        exact hin ⟨l⁻¹, MulEquiv.ext fun x => by simp [hl x]⟩
      have h1 := m12D_outer_fixSub_card (transAut m12EquivD α)
        (transAut_mul_self m12EquivD α hαinv) hout
      rw [← card_fixSub_transAut m12EquivD α]
      simpa using h1
  rcases hs.ktype with hb | hl | ha
  · have := hb.card_ge
    omega
  · rw [hl.card_eq] at hdvd
    omega
  · rw [ha.card_eq] at hdvd
    omega

end Main

end CFSG.QuasithinUnique.Id2519.Tab
