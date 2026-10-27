module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def conjSubMap (a : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj a).toMonoidHom

theorem mem_conjSubMap {a x : G} {H : Subgroup G} : x ∈ conjSubMap a H ↔ a⁻¹ * x * a ∈ H := by
  constructor
  · rintro ⟨e, he, rfl⟩
    have : a⁻¹ * (MulAut.conj a e) * a = e := by
      show a⁻¹ * (a * e * a⁻¹) * a = e
      group
    rw [← this] at he
    exact he
  · intro hx
    refine ⟨a⁻¹ * x * a, hx, ?_⟩
    show a * (a⁻¹ * x * a) * a⁻¹ = x
    group

@[expose] noncomputable def conjIso (a : G) (H : Subgroup G) : ↥H ≃* ↥(conjSubMap a H) :=
  (MulAut.conj a).subgroupMap H

theorem z_comm_E {z : G} {E S : Subgroup G} (hzS : z ∈ S)
    (hSC : S ≤ centralizer (E : Set G)) {e : G} (he : e ∈ E) : z * e = e * z :=
  ((Subgroup.mem_centralizer_iff.1 (hSC hzS)) e he).symm

theorem mem_centralizer_z_iff {z x : G} : x ∈ centralizer ({z} : Set G) ↔ z * x = x * z := by
  rw [Subgroup.mem_centralizer_iff]
  simp

namespace OI13Ctx

variable {L : Subgroup G} {z t : G} {T E : Subgroup G} {Q : Sylow 2 G} {x : G}
  {B : Subgroup G} {β : G} {S : Subgroup G} {α σ : G}

theorem exists_g1 (h : OuterS8Hyp G L z t T E Q x B β S) (c : OI13Ctx L z t T E B β S α σ)
    (hZQ : ∀ q : G, q ∈ c.Qs → q * q = 1 → ¬ ∃ g : G, q = g * z * g⁻¹)
    {y : G} (hy : OYFacts c y) {g : G} (hg : g * z * g⁻¹ = y) :
    ∃ g₁ : G, g₁ * z * g₁⁻¹ = y ∧ ∀ e : G, e ∈ E ↔ g₁ * e * g₁⁻¹ ∈ c.E0 hy := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzE : ∀ e ∈ E, z * e = e * z := fun e he => z_comm_E h.zS h.SC he
  have hE0Q : c.E0 hy ≤ c.Qs := c.E0_le_Qs hy
  set E0 : Subgroup G := c.E0 hy with hE0
  set Ep : Subgroup G := conjSubMap g⁻¹ E0 with hEp
  have mem_Ep : ∀ v, v ∈ Ep ↔ g * v * g⁻¹ ∈ E0 := by
    intro v; rw [hEp, mem_conjSubMap, inv_inv]
  have hEp_K : Ep ≤ centralizer ({z} : Set G) := by
    intro v hv
    rw [mem_centralizer_z_iff]
    have h1 := c.y_comm_E0 hy ((mem_Ep v).1 hv)
    rw [← hg] at h1
    have h2 : g * (z * v) * g⁻¹ = g * (v * z) * g⁻¹ := by
      calc g * (z * v) * g⁻¹ = (g * z * g⁻¹) * (g * v * g⁻¹) := by group
        _ = (g * v * g⁻¹) * (g * z * g⁻¹) := h1
        _ = g * (v * z) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hEp_p : IsPGroup 2 Ep := (c.E0_pgroup hy).map _
  set K : Subgroup G := centralizer ({z} : Set G) with hK
  have hTK : T ≤ K := h.outerE.cfg.T_le
  have hTmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ K → T ≤ R → R ≤ T :=
    fun R hR hRK hTR => h.outerE.cfg.T_max R hRK hR hTR
  let T' : Sylow 2 ↥K := sylowOfMax hTK h.outerE.cfg.T_pgroup hTmax
  have hEpK_p : IsPGroup 2 (Ep.subgroupOf K) :=
    hEp_p.comap_of_injective K.subtype Subtype.val_injective
  obtain ⟨P₀, hP₀⟩ := IsPGroup.exists_le_sylow hEpK_p
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K P₀ T'
  have hkey : ∀ v ∈ Ep, (k : G) * v * (k : G)⁻¹ ∈ T := by
    intro v hv
    have hvK : v ∈ K := hEp_K hv
    have hmemT : (MulAut.conj k) ⟨v, hvK⟩ ∈ (T' : Subgroup ↥K) := by
      rw [← hk, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP₀ (mem_subgroupOf.2 hv))
    exact (mem_sylowOfMax hTK h.outerE.cfg.T_pgroup hTmax).1 hmemT
  set h₀ : G := (k : G) with hh₀
  have hkz : z * h₀ = h₀ * z := mem_centralizer_z_iff.1 k.2
  set E₂ : Subgroup G := conjSubMap h₀ Ep with hE₂
  have mem_E₂ : ∀ v, v ∈ E₂ ↔ h₀⁻¹ * v * h₀ ∈ Ep := fun v => mem_conjSubMap
  have hE₂T : E₂ ≤ T := by
    intro v hv
    have h1 := hkey _ ((mem_E₂ v).1 hv)
    have e1 : h₀ * (h₀⁻¹ * v * h₀) * h₀⁻¹ = v := by group
    rw [e1] at h1
    exact h1
  obtain ⟨φ⟩ := c.E0_iso hy
  have hiso : Nonempty (↥E ≃* ↥E₂) :=
    ⟨φ.trans ((conjIso g⁻¹ E0).trans (conjIso h₀ Ep))⟩
  have hle : E₂ ≤ E ⊔ zpowers z := h.outerE.le_sup_of_equiv hE₂T hiso
  have hfus : ∀ a ∈ E, a * a = 1 → a ≠ 1 → ∃ k' : G, k' * z * k'⁻¹ = z * a := by
    intro a ha haa ha1
    obtain ⟨c', hc'L, hc'⟩ := h.outerE.econfig.conj a ha haa ha1
    have hcz : c' * z = z * c' := h.outerE.cfg.z_comm_of_mem_A hc'L
    refine ⟨c' * x, ?_⟩
    calc c' * x * z * (c' * x)⁻¹ = c' * (x * z * x⁻¹) * c'⁻¹ := by group
      _ = c' * (z * t) * c'⁻¹ := by rw [h.x_z]
      _ = z * (c' * t * c'⁻¹) := by
          calc c' * (z * t) * c'⁻¹ = (c' * z) * t * c'⁻¹ := by group
            _ = (z * c') * t * c'⁻¹ := by rw [hcz]
            _ = z * (c' * t * c'⁻¹) := by group
      _ = z * a := by rw [← hc']
  have hE2E0 : ∀ v ∈ E₂, (g * h₀⁻¹) * v * (g * h₀⁻¹)⁻¹ ∈ E0 := by
    intro v hv
    have e2 : (g * h₀⁻¹) * v * (g * h₀⁻¹)⁻¹ = g * (h₀⁻¹ * v * h₀) * g⁻¹ := by group
    rw [e2]
    exact (mem_Ep _).1 ((mem_E₂ v).1 hv)
  have hnc : ∀ u ∈ E₂, u * u = 1 → ∀ k' : G, u ≠ k' * z * k'⁻¹ := by
    intro u hu huu k' huk
    have hq := hE2E0 u hu
    have hqq : ((g * h₀⁻¹) * u * (g * h₀⁻¹)⁻¹) * ((g * h₀⁻¹) * u * (g * h₀⁻¹)⁻¹) = 1 := by
      calc ((g * h₀⁻¹) * u * (g * h₀⁻¹)⁻¹) * ((g * h₀⁻¹) * u * (g * h₀⁻¹)⁻¹)
          = (g * h₀⁻¹) * (u * u) * (g * h₀⁻¹)⁻¹ := by group
        _ = 1 := by rw [huu]; group
    exact hZQ _ (hE0Q hq) hqq ⟨g * h₀⁻¹ * k', by rw [huk]; group⟩
  have hzpow : zpowers z ≤ centralizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 (fun e he => (hzE e he).symm)
  have htE : t ∈ E := c.h.t_mem_E
  have hinvE : ∀ u ∈ E₂, u * u = 1 → u ∈ E := by
    intro u hu huu
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hzpow (hle hu)
    rcases mem_zpowers_sq_eq_one h.outerE.cfg.z_sq hb with hb1 | hb1
    · rw [hab, hb1, mul_one]; exact ha
    · exfalso
      rw [hb1] at hab
      have haa : a * a = 1 := by
        have e3 : (a * z) * (a * z) = (a * a) * (z * z) := by
          calc (a * z) * (a * z) = a * (z * a) * z := by group
            _ = a * (a * z) * z := by rw [hzE a ha]
            _ = (a * a) * (z * z) := by group
        have huu' : (a * z) * (a * z) = 1 := by rw [← hab]; exact huu
        have e4 := e3.symm.trans huu'
        rwa [h.outerE.cfg.z_sq, mul_one] at e4
      by_cases ha1 : a = 1
      · rw [ha1, one_mul] at hab
        exact hnc u hu huu 1 (by rw [hab]; group)
      by_cases hat : a = t
      · exact hnc u hu huu x (by rw [h.x_z, hab, hat, hzE t htE])
      · obtain ⟨k', hk'⟩ := hfus a ha haa ha1
        exact hnc u hu huu k' (by rw [hab, hk']; exact (hzE a ha).symm)
  have hgen : E₂ ≤ E := by
    set A : Subgroup G := (closure {v : ↥E | v * v = 1 ∧ v ≠ 1}).map E.subtype with hA
    have hgens : ∀ e : G, e ∈ E → e * e = 1 → e ≠ 1 → e ∈ A := by
      intro e he hee hne
      refine ⟨⟨e, he⟩, subset_closure ⟨?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        simpa using hee
      · intro h1
        exact hne (congrArg Subtype.val h1)
    have hEA : ∀ e ∈ E, e ∈ A := by
      intro e he
      rw [h.outerE.econfig.gen] at he
      exact ((Subgroup.closure_le A).2 (fun e' he' => hgens e' he'.1 he'.2.1 he'.2.2)) he
    have htop : ∀ v : ↥E, v ∈ closure {w : ↥E | w * w = 1 ∧ w ≠ 1} := by
      intro v
      obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 (hEA v v.2)
      have hwv' : w = v := Subtype.ext hwv
      rw [← hwv']
      exact hw
    obtain ⟨ψ⟩ := hiso
    have hψ : ∀ v : ↥E, (ψ v : G) ∈ E := by
      intro v
      have h1 : ψ.toMonoidHom v ∈ (closure {w : ↥E | w * w = 1 ∧ w ≠ 1}).map ψ.toMonoidHom :=
        Subgroup.mem_map_of_mem _ (htop v)
      rw [MonoidHom.map_closure] at h1
      have h2 : closure (ψ.toMonoidHom '' {w : ↥E | w * w = 1 ∧ w ≠ 1}) ≤ E.subgroupOf E₂ := by
        apply (Subgroup.closure_le _).2
        rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
        rw [SetLike.mem_coe, mem_subgroupOf]
        apply hinvE _ (ψ.toMonoidHom w).2
        have hww : ψ.toMonoidHom w * ψ.toMonoidHom w = 1 := by
          rw [← map_mul, hw1, map_one]
        have h3 := congrArg Subtype.val hww
        simpa using h3
      exact mem_subgroupOf.1 (h2 h1)
    intro e he
    have hv := hψ (ψ.symm ⟨e, he⟩)
    rw [MulEquiv.apply_symm_apply] at hv
    exact hv
  have hE2eq : E₂ = E := by
    apply Subgroup.eq_of_le_of_card_ge hgen
    obtain ⟨ψ⟩ := hiso
    exact le_of_eq (Nat.card_congr ψ.toEquiv)
  refine ⟨g * h₀⁻¹, ?_, ?_⟩
  · have hz0 : h₀⁻¹ * z * h₀ = z := by
      calc h₀⁻¹ * z * h₀ = h₀⁻¹ * (z * h₀) := by group
        _ = h₀⁻¹ * (h₀ * z) := by rw [hkz]
        _ = z := by group
    calc g * h₀⁻¹ * z * (g * h₀⁻¹)⁻¹ = g * (h₀⁻¹ * z * h₀) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hz0]
      _ = y := hg
  · intro e
    constructor
    · intro he
      have he2 : e ∈ E₂ := by rw [hE2eq]; exact he
      exact hE2E0 e he2
    · intro he
      have he2 : e ∈ E₂ := by
        rw [mem_E₂, mem_Ep]
        have e5 : g * (h₀⁻¹ * e * h₀) * g⁻¹ = g * h₀⁻¹ * e * (g * h₀⁻¹)⁻¹ := by group
        rw [e5]
        exact he
      rw [← hE2eq]
      exact he2

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
