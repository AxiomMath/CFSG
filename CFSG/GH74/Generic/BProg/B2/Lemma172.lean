module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Uniqueness.Statements
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped Pointwise

namespace Lemma172

section Conj

variable {G : Type} [Group G]

private theorem isConj_iff' {a b : G} : IsConj a b ↔ ∃ g : G, g⁻¹ * a * g = b := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c⁻¹, by simpa using hc⟩
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by simpa using hg⟩

private theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf b = orderOf a := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj c) a

theorem mem_of_conj_mem {M : Subgroup G} {y : G} (hy : InJ2M M y) (hf : ControlsFusionElt M y)
    {g : G} (h : g⁻¹ * y * g ∈ M) : g ∈ M := by
  obtain ⟨m, hm, hmg⟩ := hf g h
  have hc : m * g⁻¹ ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * g⁻¹ * y = m * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = m * (m⁻¹ * y * m) * g⁻¹ := by rw [hmg]
      _ = y * (m * g⁻¹) := by group
  have hg : g⁻¹ ∈ M := by
    have e : g⁻¹ = m⁻¹ * (m * g⁻¹) := by group
    rw [e]
    exact M.mul_mem (M.inv_mem hm) (hy.2.2 hc)
  simpa using M.inv_mem hg

private theorem exists_conj_le_sylow_two {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsPGroup 2 E) (P : Sylow 2 X) :
    ∃ g : X, E.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨g, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 : MulAut.conj g • y ∈ MulAut.conj g • (Q : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Q : Subgroup X) (hQ hy)
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact h1

end Conj

end Lemma172

theorem lemma172 {G : Type} [Group G] [Finite G] {M : Subgroup G} (hM : M ≠ ⊤) {v : G}
    (hv : InJ2M M v) (hvf : ControlsFusionElt M v)
    (hprod : ∀ m ∈ M, v * (m⁻¹ * v * m) = (m⁻¹ * v * m) * v → m⁻¹ * v * m ≠ v →
      InJ2M M (v * (m⁻¹ * v * m)) ∧ ControlsFusionElt M (v * (m⁻¹ * v * m))) :
    IsInvariantInvolutionSet {y : G | IsConj v y} ∧ IsProductDisconnected {y : G | IsConj v y} M := by
  have key : ∀ k : G, k⁻¹ * v * k ∈ M → k ∈ M := fun k hk => Lemma172.mem_of_conj_mem hv hvf hk
  have hvv : v * v = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one v
    rwa [hv.2.1] at this
  refine ⟨?_, ?_⟩
  · unfold IsInvariantInvolutionSet
    refine ⟨fun z hz => ?_, fun z hz g => ?_⟩
    · rw [Lemma172.orderOf_eq_of_isConj hz]
      exact hv.2.1
    · obtain ⟨k, rfl⟩ := Lemma172.isConj_iff'.1 hz
      exact Lemma172.isConj_iff'.2 ⟨k * g, by group⟩
  · unfold IsProductDisconnected
    refine ⟨hM, ⟨v, IsConj.refl v, hv.1⟩, ?_, ?_⟩
    ·
      intro z hz hzM g
      obtain ⟨k, rfl⟩ := Lemma172.isConj_iff'.1 hz
      have hk : k ∈ M := key k hzM
      constructor
      · intro h
        have h1 : k * g ∈ M := by
          apply key
          have e : (k * g)⁻¹ * v * (k * g) = g⁻¹ * (k⁻¹ * v * k) * g := by group
          rw [e]
          exact h
        have e2 : g = k⁻¹ * (k * g) := by group
        rw [e2]
        exact M.mul_mem (M.inv_mem hk) h1
      · intro hg
        exact M.mul_mem (M.mul_mem (M.inv_mem hg) hzM) hg
    ·
      intro u hu huM
      obtain ⟨hu2, x, hx, z, hz, hxz, rfl⟩ := hu
      obtain ⟨a, rfl⟩ := Lemma172.isConj_iff'.1 hx
      obtain ⟨b, rfl⟩ := Lemma172.isConj_iff'.1 hz
      obtain ⟨u, hu⟩ : ∃ u : G, u = a⁻¹ * v * a * (b⁻¹ * v * b) := ⟨_, rfl⟩
      have hxz' : a⁻¹ * v * a * (b⁻¹ * v * b) = b⁻¹ * v * b * (a⁻¹ * v * a) := hxz
      have hcomm : v * ((b * a⁻¹)⁻¹ * v * (b * a⁻¹)) = ((b * a⁻¹)⁻¹ * v * (b * a⁻¹)) * v := by
        have h1 : v * ((b * a⁻¹)⁻¹ * v * (b * a⁻¹)) = a * (a⁻¹ * v * a * (b⁻¹ * v * b)) * a⁻¹ := by
          group
        have h2 : ((b * a⁻¹)⁻¹ * v * (b * a⁻¹)) * v = a * (b⁻¹ * v * b * (a⁻¹ * v * a)) * a⁻¹ := by
          group
        rw [h1, h2, hxz']
      have hne : (b * a⁻¹)⁻¹ * v * (b * a⁻¹) ≠ v := by
        intro h
        have h1 : a⁻¹ * v * a * (b⁻¹ * v * b) = 1 := by
          have e : a⁻¹ * v * a * (b⁻¹ * v * b)
              = a⁻¹ * (v * ((b * a⁻¹)⁻¹ * v * (b * a⁻¹))) * a := by group
          rw [e, h, hvv]
          group
        rw [h1, orderOf_one] at hu2
        exact absurd hu2 (by norm_num)
      have hz'M : (b * a⁻¹)⁻¹ * v * (b * a⁻¹) ∈ M :=
        hv.2.2 (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
      have hm'M : b * a⁻¹ ∈ M := key _ hz'M
      obtain ⟨hw, hwf⟩ := hprod (b * a⁻¹) hm'M hcomm hne
      have hw_eq : v * ((b * a⁻¹)⁻¹ * v * (b * a⁻¹)) = a * u * a⁻¹ := by
        rw [hu]
        group
      have hu_eq : a⁻¹ * (v * ((b * a⁻¹)⁻¹ * v * (b * a⁻¹))) * a = u := by
        rw [hw_eq]
        group
      have huM' : u ∈ M := by
        rw [hu]
        exact huM
      have haM : a ∈ M := Lemma172.mem_of_conj_mem hw hwf (by rw [hu_eq]; exact huM')
      intro c hc
      have hc' : c * u = u * c := by
        have := Subgroup.mem_centralizer_singleton_iff.1 hc
        rw [hu]
        exact this
      have hcw : a * c * a⁻¹ ∈ centralizer ({v * ((b * a⁻¹)⁻¹ * v * (b * a⁻¹))} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff, hw_eq]
        calc a * c * a⁻¹ * (a * u * a⁻¹) = a * (c * u) * a⁻¹ := by group
          _ = a * (u * c) * a⁻¹ := by rw [hc']
          _ = a * u * a⁻¹ * (a * c * a⁻¹) := by group
      have h1 : a * c * a⁻¹ ∈ M := hw.2.2 hcw
      have e : c = a⁻¹ * (a * c * a⁻¹) * a := by group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem haM) h1) haM

theorem prop92C {G : Type} [Group G] [Finite G] {M : Subgroup G} (h2 : Stage2Concl2C M) {y₁ y₂ : G}
    (hconj : ∃ g : G, g * y₁ * g⁻¹ = y₂) {B : Subgroup G} (hB : InU0C M B)
    (hBy : ∀ b ∈ B, b * y₁ = y₁ * b) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer ({y₂} : Set G))) (hSM : S ≤ M) :
    ∃ m ∈ M, m * y₁ * m⁻¹ = y₂ := by
  obtain ⟨g, hg⟩ := hconj
  set C : Subgroup G := centralizer ({y₂} : Set G) with hC
  obtain ⟨-, hBel, -⟩ := hB.1
  have hBp : IsPGroup 2 B := IsElementaryAbelian.isPGroup 2 B
  set H : Subgroup G := B.map (MulAut.conj g).toMonoidHom with hH
  have hHC : H ≤ C := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    show (g * b * g⁻¹) * y₂ = y₂ * (g * b * g⁻¹)
    rw [← hg]
    calc (g * b * g⁻¹) * (g * y₁ * g⁻¹) = g * (b * y₁) * g⁻¹ := by group
      _ = g * (y₁ * b) * g⁻¹ := by rw [hBy b hb]
      _ = (g * y₁ * g⁻¹) * (g * b * g⁻¹) := by group
  have hHp : IsPGroup 2 H := hBp.map _
  obtain ⟨Q, hQ⟩ := hS
  have hH' : IsPGroup 2 (H.subgroupOf C) := hHp.comap_subtype
  obtain ⟨c, hc⟩ := Lemma172.exists_conj_le_sylow_two hH' Q
  have hcg : ∀ b ∈ B, ((c : G) * (g * b * g⁻¹) * (c : G)⁻¹) ∈ S := by
    intro b hb
    have hmem : (⟨g * b * g⁻¹, hHC ⟨b, hb, rfl⟩⟩ : C) ∈ H.subgroupOf C :=
      Subgroup.mem_subgroupOf.2 ⟨b, hb, rfl⟩
    have h1 := hc ⟨_, hmem, rfl⟩
    rw [← hQ]
    exact ⟨_, h1, rfl⟩
  have hcgM : conjugate B ((c : G) * g)⁻¹ ≤ M := by
    rintro _ ⟨b, hb, rfl⟩
    refine hSM ?_
    have e : (MulAut.conj ((c : G) * g)⁻¹⁻¹).toMonoidHom b =
        (c : G) * (g * b * g⁻¹) * (c : G)⁻¹ := by
      show ((c : G) * g)⁻¹⁻¹ * b * ((c : G) * g)⁻¹⁻¹⁻¹ = _
      group
    rw [e]
    exact hcg b hb
  have hmM : ((c : G) * g)⁻¹ ∈ M := h2 B hB _ hcgM
  refine ⟨(c : G) * g, by simpa using M.inv_mem hmM, ?_⟩
  have hcy : (c : G) * y₂ = y₂ * (c : G) := by
    have hcmem : (c : G) ∈ centralizer ({y₂} : Set G) := c.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hcmem
    exact hcmem
  calc (c : G) * g * y₁ * ((c : G) * g)⁻¹ = (c : G) * (g * y₁ * g⁻¹) * (c : G)⁻¹ := by group
    _ = (c : G) * y₂ * (c : G)⁻¹ := by rw [hg]
    _ = y₂ := by rw [hcy]; group

end CFSG.GH74.Generic.BProg.B2
