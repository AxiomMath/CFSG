module

public import CFSG.GH74.GLS.Stage1.Main.BrPair
public import CFSG.GH74.GLS.IVK.Lifted.YUnique
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue710b

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
open scoped commutatorElement

namespace L79

@[expose] def IVK412Nc : Prop :=
  ∀ {K : Type} [Group K] [Finite K] {q : ℕ}, Odd q → 5 ≤ q →
    ((q % 4 = 3 ∧ IVK.IsLnEps 4 K 1 q) ∨ (q % 4 = 1 ∧ IVK.IsLnEps 4 K (-1) q)) →
    ∀ {u : K}, orderOf u = 2 → ¬ CFSG.GH74.IsCentralInvolution u →
      ∀ (S : Sylow 2 ↥(centralizer ({u} : Set K))),
        ∃ (D₁ D₂ : Subgroup K) (n : ℕ), 3 ≤ n ∧
          S.map (centralizer ({u} : Set K)).subtype = D₁ ⊔ D₂ ∧
          (∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) ∧ D₁ ⊓ D₂ = ⊥ ∧
          IVK.IsDihedralTwoGroup ↥D₁ n ∧ IVK.IsDihedralTwoGroup ↥D₂ n ∧
          ((∀ a ∈ D₁, u * a = a * u) ∧ u ∈ D₁ ∨ (∀ a ∈ D₂, u * a = a * u) ∧ u ∈ D₂) ∧
          Nat.card ↥(S.map (centralizer ({u} : Set K)).subtype) = 2 ^ (2 * n) ∧
          ∀ T : Sylow 2 K, Nat.card ↥(T : Subgroup K) = 2 ^ (2 * n + 1)

theorem relIndex_inf_centralizer_eq_two {G : Type*} [Group G] {S : Subgroup G} {z u : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ s ∈ S, s * z = z * s)
    (hnorm : ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z)
    (hex : ∃ a ∈ S, a * u ≠ u * a) :
    (S ⊓ centralizer ({u} : Set G)).relIndex S = 2 := by
  obtain ⟨a, haS, hau⟩ := hex
  have hmem : ∀ s ∈ S, (s ∈ centralizer ({u} : Set G) ↔ s * u * s⁻¹ = u) := by
    intro s _
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hconj : ∀ s ∈ S, s * z * s⁻¹ = z := by
    intro s hs
    rw [hzc s hs]
    group
  have hauz : a * u * a⁻¹ = u * z := by
    rcases hnorm a haS with h | h
    · exact absurd ((mul_inv_eq_iff_eq_mul.1 h)) hau
    · exact h
  have hne : u * z ≠ u := fun h => hz1 (by simpa using h)
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨a, haS⟩, fun b => ?_⟩
  have hbS : (b : G) ∈ S := b.2
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  rw [hmem _ (S.mul_mem hbS haS), hmem _ hbS]
  have hba : (b : G) * a * u * ((b : G) * a)⁻¹ = (b : G) * (a * u * a⁻¹) * (b : G)⁻¹ := by group
  rcases hnorm b hbS with hb | hb
  · have : (b : G) * a * u * ((b : G) * a)⁻¹ = u * z := by
      rw [hba, hauz]
      calc (b : G) * (u * z) * (b : G)⁻¹
          = ((b : G) * u * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by group
        _ = u * z := by rw [hb, hconj b hbS]
    simp only [hbS, true_and, S.mul_mem hbS haS]
    rw [this]
    simp [hb, hne]
  · have : (b : G) * a * u * ((b : G) * a)⁻¹ = u := by
      rw [hba, hauz]
      calc (b : G) * (u * z) * (b : G)⁻¹
          = ((b : G) * u * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by group
        _ = u := by
          rw [hb, hconj b hbS]
          calc u * z * z = u * (z * z) := by group
            _ = u := by rw [hz2]; simp
    simp only [hbS, true_and, S.mul_mem hbS haS]
    rw [this, hb]
    simp [hne]

theorem syl2In_inf_centralizer_of_index_two {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hS : Syl2In S ⊤) {z u : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ s ∈ S, s * z = z * s)
    (hnorm : ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z)
    (hnc : ∀ g : G, ∃ s ∈ S, s * (g * u * g⁻¹) ≠ (g * u * g⁻¹) * s) :
    Syl2In (S ⊓ centralizer ({u} : Set G)) (centralizer ({u} : Set G)) ∧
      2 * Nat.card ↥(S ⊓ centralizer ({u} : Set G)) = Nat.card ↥S := by
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  have hex : ∃ a ∈ S, a * u ≠ u * a := by
    obtain ⟨s, hs, h⟩ := hnc 1
    exact ⟨s, hs, by simpa using h⟩
  have hidx := relIndex_inf_centralizer_eq_two hz2 hz1 hzc hnorm hex
  have hcard : 2 * Nat.card ↥(S ⊓ C) = Nat.card ↥S := by
    have h := Subgroup.relIndex_mul_card (H := S ⊓ C) (K := S)
    rw [hidx, inf_eq_left.2 (inf_le_left : S ⊓ C ≤ S)] at h
    exact h
  have hApg : IsPGroup 2 ↥(S ⊓ C) := hS.2.1.to_inf_left
  have hbound : ∀ V : Subgroup G, IsPGroup 2 ↥V → V ≤ C → 2 * Nat.card ↥V ≤ Nat.card ↥S := by
    intro V hV hVC
    obtain ⟨P, hP, hVP⟩ := exists_syl2In_ge hV (le_top : V ≤ ⊤)
    obtain ⟨c, -, hc⟩ := hS.exists_conj hP
    have hPcard : Nat.card ↥P = Nat.card ↥S := by rw [hc, cj_card]
    have hnotle : ¬ P ≤ C := by
      intro hPC
      obtain ⟨s, hs, hne⟩ := hnc c
      apply hne
      have hx : c⁻¹ * s * c ∈ P := by
        rw [hc, mem_cj]
        simpa [mul_assoc] using hs
      have hxu := Subgroup.mem_centralizer_singleton_iff.1 (hPC hx)
      calc s * (c * u * c⁻¹) = c * ((c⁻¹ * s * c) * u) * c⁻¹ := by group
        _ = c * (u * (c⁻¹ * s * c)) * c⁻¹ := by rw [hxu]
        _ = (c * u * c⁻¹) * s := by group
    have hrel : C.relIndex P ≠ 1 := fun h => hnotle (Subgroup.relIndex_eq_one.1 h)
    have hmul := Subgroup.relIndex_mul_card (H := C) (K := P)
    have hpos : 0 < Nat.card ↥P := Nat.card_pos
    have h0 : C.relIndex P ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      omega
    have h2 : 2 ≤ C.relIndex P := by omega
    have hle : Nat.card ↥V ≤ Nat.card ↥(C ⊓ P) :=
      Subgroup.card_le_of_le (le_inf hVC hVP)
    calc 2 * Nat.card ↥V ≤ 2 * Nat.card ↥(C ⊓ P) := by omega
      _ ≤ C.relIndex P * Nat.card ↥(C ⊓ P) := Nat.mul_le_mul_right _ h2
      _ = Nat.card ↥S := by rw [hmul, hPcard]
  obtain ⟨Sy, hSy, hASy⟩ := exists_syl2In_ge hApg (inf_le_right : S ⊓ C ≤ C)
  have hSyb := hbound Sy hSy.2.1 hSy.1
  have hEq : S ⊓ C = Sy := Subgroup.eq_of_le_of_card_ge hASy (by omega)
  refine ⟨?_, hcard⟩
  rw [hEq]
  exact hSy

theorem model_structure (h412 : IVK412Nc) {Gs : Type} [Group Gs] [Finite Gs] {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : (q % 4 = 3 ∧ IVK.IsLnEps 4 Gs 1 q) ∨ (q % 4 = 1 ∧ IVK.IsLnEps 4 Gs (-1) q))
    (S' : Sylow 2 Gs) {u' : Gs} (hu'2 : orderOf u' = 2) (hnc : ¬ CFSG.GH74.IsCentralInvolution u')
    (hcard : 2 * Nat.card ↥((S' : Subgroup Gs) ⊓ centralizer ({u'} : Set Gs)) = Nat.card ↥(S' : Subgroup Gs)) :
    ∃ (D₁ D₂ : Subgroup Gs) (n : ℕ), 3 ≤ n ∧
      (S' : Subgroup Gs) ⊓ centralizer ({u'} : Set Gs) = D₁ ⊔ D₂ ∧
      (∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) ∧ D₁ ⊓ D₂ = ⊥ ∧
      IVK.IsDihedralTwoGroup ↥D₁ n ∧ IVK.IsDihedralTwoGroup ↥D₂ n ∧
      (∀ a ∈ D₁, u' * a = a * u') ∧ u' ∈ D₁ := by
  set C : Subgroup Gs := centralizer ({u'} : Set Gs) with hC
  set A : Subgroup Gs := (S' : Subgroup Gs) ⊓ C with hA
  have hApg : IsPGroup 2 ↥A := S'.isPGroup'.to_inf_left
  obtain ⟨P, hP, hAP⟩ := exists_syl2In_ge hApg (inf_le_right : A ≤ C)
  obtain ⟨D₁, D₂, n, hn, hmap, hcomm, hinf, hd1, hd2, hcen, hSyc, hT⟩ := h412 hq h5 hK hu'2 hnc (toSylow hP)
  have hmapP : (toSylow hP).map C.subtype = P := by
    show ((toSylow hP : Subgroup ↥C)).map C.subtype = P
    rw [coe_toSylow hP]
    exact Subgroup.map_subgroupOf_eq_of_le hP.1
  rw [hmapP] at hmap hSyc
  have hS'card : Nat.card ↥(S' : Subgroup Gs) = 2 ^ (2 * n + 1) := hT S'
  have hAeq : A = P := by
    refine Subgroup.eq_of_le_of_card_ge hAP ?_
    rw [hSyc]
    have : 2 * Nat.card ↥A = 2 * 2 ^ (2 * n) := by
      rw [hcard, hS'card]
      ring
    omega
  have hsup : A = D₁ ⊔ D₂ := hAeq.trans hmap
  rcases hcen with ⟨hc1, hu1⟩ | ⟨hc2, hu2⟩
  · exact ⟨D₁, D₂, n, hn, hsup, hcomm, hinf, hd1, hd2, hc1, hu1⟩
  · refine ⟨D₂, D₁, n, hn, by rw [hsup, sup_comm], fun a ha b hb => (hcomm b hb a ha).symm,
      by rw [inf_comm]; exact hinf, hd2, hd1, hc2, hu2⟩

def pullback {G Gs : Type} [Group G] [Group Gs] {S : Subgroup G} {f : G → Gs} (hf : Tr.FHom S f)
    (D : Subgroup Gs) : Subgroup G where
  carrier := {g | g ∈ S ∧ f g ∈ D}
  mul_mem' := fun {a b} ha hb =>
    ⟨S.mul_mem ha.1 hb.1, by rw [hf.mul a ha.1 b hb.1]; exact D.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨S.one_mem, by rw [hf.map_one]; exact D.one_mem⟩
  inv_mem' := fun {a} ha => ⟨S.inv_mem ha.1, by rw [hf.map_inv ha.1]; exact D.inv_mem ha.2⟩

def pullbackHom {G Gs : Type} [Group G] [Group Gs] {S : Subgroup G} {f : G → Gs} (hf : Tr.FHom S f)
    (D : Subgroup Gs) : ↥(pullback hf D) →* ↥D where
  toFun g := ⟨f g, g.2.2⟩
  map_one' := Subtype.ext hf.map_one
  map_mul' a b := Subtype.ext (hf.mul a a.2.1 b b.2.1)

noncomputable def pullbackEquiv {G Gs : Type} [Group G] [Group Gs] {S : Subgroup G} {f : G → Gs}
    (hf : Tr.FHom S f) {D : Subgroup Gs} (hD : ∀ d ∈ D, ∃ s ∈ S, f s = d) :
    ↥(pullback hf D) ≃* ↥D :=
  MulEquiv.ofBijective (pullbackHom hf D)
    ⟨fun a b hab => Subtype.ext (hf.inj a a.2.1 b b.2.1 (congrArg Subtype.val hab)),
      fun d => by
        obtain ⟨s, hs, hsd⟩ := hD d d.2
        exact ⟨⟨s, hs, hsd ▸ d.2⟩, Subtype.ext hsd⟩⟩

theorem isDihedralTwoGroup_pullback {G Gs : Type} [Group G] [Group Gs] {S : Subgroup G} {f : G → Gs}
    (hf : Tr.FHom S f) {D : Subgroup Gs} (hD : ∀ d ∈ D, ∃ s ∈ S, f s = d) {n : ℕ}
    (h : IVK.IsDihedralTwoGroup ↥D n) : IVK.IsDihedralTwoGroup ↥(pullback hf D) n := by
  obtain ⟨hn, k, hk, hk2, ⟨e⟩⟩ := h
  exact ⟨hn, k, hk, hk2, ⟨(pullbackEquiv hf hD).trans e⟩⟩

def cjEquiv {G : Type} [Group G] (H : Subgroup G) (g : G) : ↥(cj H g) ≃* ↥H where
  toFun a := ⟨g * a * g⁻¹, a.2⟩
  invFun b := ⟨g⁻¹ * b * g, by simp [mem_cj, mul_assoc]⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv b := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem isDihedralTwoGroup_cj {G : Type} [Group G] {H : Subgroup G} (g : G) {n : ℕ}
    (h : IVK.IsDihedralTwoGroup ↥H n) : IVK.IsDihedralTwoGroup ↥(cj H g) n := by
  obtain ⟨hn, k, hk, hk2, ⟨e⟩⟩ := h
  exact ⟨hn, k, hk, hk2, ⟨(cjEquiv H g).trans e⟩⟩

theorem exists_fhom_of_psi {G : Type} [Group G] {z : G} {X S P : Subgroup G} {t w : G} {Gs : Type}
    [Group Gs] {E S' : Subgroup Gs} {t' w' z' : Gs} (hSX : S ≤ X) (hPS : P ≤ S)
    (hSO : S ⊓ Oz z = ⊥) (hzS : z ∈ S) (hz1 : z ≠ 1) (hzc : ∀ s ∈ S, s * z = z * s)
    (hz'2 : z' * z' = 1)
    (hZ' : (center ↥S').map S'.subtype = zpowers z')
    (hψ : PsiData7 z X S P t w E S' t' w') :
    ∃ f : G → Gs, Tr.FHom S f ∧ (∀ s ∈ S, f s ∈ S') ∧ (∀ s ∈ P, f s ∈ E) ∧
      (∀ a ∈ S', ∃ s ∈ S, f s = a) ∧ f z = z' := by
  obtain ⟨hN, ψ, ⟨hS1, hS2⟩, ⟨hP1, -⟩, -, -⟩ := hψ
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥X →* Gs, ∀ u : ↥X, φ u = ((ψ (QuotientGroup.mk u) : ↥(E ⊔ S')) : Gs) :=
    ⟨(E ⊔ S').subtype.comp (ψ.toMonoidHom.comp (QuotientGroup.mk' ((Oz z).subgroupOf X))),
      fun u => rfl⟩
  obtain ⟨f, hfv⟩ : ∃ f : G → Gs, ∀ g (hg : g ∈ S), f g = φ ⟨g, hSX hg⟩ :=
    ⟨fun g => if hg : g ∈ S then φ ⟨g, hSX hg⟩ else 1, fun g hg => by simp [hg]⟩
  have hhom : Tr.FHom S f := by
    refine ⟨fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩
    · rw [hfv (a * b) (S.mul_mem ha hb), hfv a ha, hfv b hb]
      exact map_mul φ ⟨a, hSX ha⟩ ⟨b, hSX hb⟩
    · rw [hfv a ha, hfv b hb, hφ, hφ] at hab
      have h1 : ψ (QuotientGroup.mk (⟨a, hSX ha⟩ : ↥X)) = ψ (QuotientGroup.mk (⟨b, hSX hb⟩ : ↥X)) :=
        Subtype.ext hab
      have h2 := QuotientGroup.eq.1 (ψ.injective h1)
      have h3 : a⁻¹ * b ∈ Oz z := Subgroup.mem_subgroupOf.1 h2
      have h4 : a⁻¹ * b ∈ S ⊓ Oz z := ⟨S.mul_mem (S.inv_mem ha) hb, h3⟩
      rw [hSO, Subgroup.mem_bot] at h4
      exact inv_mul_eq_one.1 h4
  have hfS : ∀ s ∈ S, f s ∈ S' := fun s hs => by
    rw [hfv s hs, hφ]
    exact hS1 ⟨s, hSX hs⟩ hs
  have hfP : ∀ s ∈ P, f s ∈ E := fun s hs => by
    rw [hfv s (hPS hs), hφ]
    exact hP1 ⟨s, hSX (hPS hs)⟩ hs
  have hsurj : ∀ a ∈ S', ∃ s ∈ S, f s = a := by
    intro a ha
    obtain ⟨s, hsS, hs⟩ := hS2 (ψ.symm ⟨a, (le_sup_right : S' ≤ E ⊔ S') ha⟩) (by simpa using ha)
    refine ⟨(s : G), hsS, ?_⟩
    rw [hfv (s : G) hsS, hφ]
    show ((ψ (QuotientGroup.mk s) : ↥(E ⊔ S')) : Gs) = a
    rw [hs, MulEquiv.apply_symm_apply]
  have hfz : f z = z' := by
    have hcomm : ∀ x ∈ S', x * f z = f z * x := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := hsurj x hx
      rw [← hhom.mul s hs z hzS, ← hhom.mul z hzS s hs, hzc s hs]
    have hmem : f z ∈ (center ↥S').map S'.subtype := by
      refine ⟨⟨f z, hfS z hzS⟩, Subgroup.mem_center_iff.2 (fun g => ?_), rfl⟩
      exact Subtype.ext (hcomm g.1 g.2)
    rw [hZ'] at hmem
    rcases (mem_zpowers_of_sq hz'2).1 hmem with h1 | h1
    · exact absurd h1 (hhom.ne_one hzS hz1)
    · exact h1
  exact ⟨f, hhom, hfS, hfP, hsurj, hfz⟩

theorem l79_of_ivk412 (hII : II4_4_4_center) (h44 : Thm2.Recip.II4_44) (h412 : IVK412Nc) : L79_C_S_u := by
  intro G _ _ z S K₁ K₂ t u q w h hc hw x hx V hV
  classical
  have hM := h.m4 hII
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have hzS := h.z_mem_S hII
  have hSsyl : Syl2In S ⊤ := hM.S_top
  have hzc : ∀ s ∈ S, s * z = z * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hs)
  have hSO := h.S_inf_Oz hII
  have hPS : Pz S z ≤ S := (h.Pz_le_S1 hII).trans Cfg7.S1_le_S
  have hX : S ≤ K₁ ⊔ K₂ ⊔ S := le_sup_right
  obtain ⟨F, iF, fF, hFq, -⟩ := id h.ch.hq₁
  obtain ⟨Gs, iGs, fGs, p, e, hGs, hmod⟩ := exists_model7 h.ch.q_odd h.ch.q_ge (w = 1) hFq
  have hLU : (q % 4 = 3 ∧ IVK.IsLnEps 4 Gs 1 q) ∨ (q % 4 = 1 ∧ IVK.IsLnEps 4 Gs (-1) q) := by
    rcases hmod with ⟨hw1, -⟩ | ⟨-, hLU⟩
    · exact absurd hw1 hw
    · exact hLU
  have hSp : IVK.IsSp4L4U4 Gs q := Or.inr hLU
  obtain ⟨S'⟩ : Nonempty (Sylow 2 Gs) := inferInstance
  obtain ⟨z', hz'o, hcenS'⟩ := modelCenter Gs p e hGs S'
  have hz'mem : z' ∈ ((center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype) := by
    rw [hcenS']
    exact mem_zpowers z'
  obtain ⟨c, hc', hcz⟩ := hz'mem
  have hcz' : (c : Gs) = z' := hcz
  have hz'S' : z' ∈ (S' : Subgroup Gs) := hcz' ▸ c.2
  have hz'c : ∀ x ∈ (S' : Subgroup Gs), x * z' = z' * x := by
    intro x hx
    have := Subgroup.mem_center_iff.1 hc' ⟨x, hx⟩
    rw [← hcz']
    exact congrArg Subtype.val this
  have hz'2 : z' * z' = 1 := (orderOf_two_iff.1 hz'o).1
  have hz'1 : z' ≠ 1 := (orderOf_two_iff.1 hz'o).2
  obtain ⟨t', w', E₁, E₂, ht'S, hw'S, ht'o, hw'o, hcomm', hprod', hinter', ht'c, hEz, hE₂, hsl2,
      hinterE, hcommE, hnormE, hw1iff, hcls, htzne, hEfus, hpgl, hwfus, hcentral⟩ :=
    ivk_4_10 Gs q h.ch.q_odd h.ch.q_ge hSp S' z' hz'S' hz'o hz'c
  have hdat : Dat410 q z' (S' : Subgroup Gs) t' w' E₁ E₂ :=
    ⟨ht'S, hw'S, ht'o, hw'o, hcomm'.eq, hprod', hinter', ht'c, hEz, hE₂, hsl2, hinterE, hcommE,
      hnormE, hcls, htzne, hEfus, hpgl, hwfus⟩
  have hww : w' = 1 ↔ w = 1 := by
    rcases hmod with ⟨hw1, hP⟩ | ⟨hw1, hLU'⟩
    · exact ⟨fun _ => hw1, fun _ => hw1iff.2 hP⟩
    · have hnP : ¬IVK.IsPSp4 Gs q := fun hP => by
        rcases hLU' with ⟨-, hl⟩ | ⟨-, hl⟩
        · exact (ivk_PSp4_ne_LU Gs q hP).1 hl
        · exact (ivk_PSp4_ne_LU Gs q hP).2 hl
      exact ⟨fun h1 => absurd (hw1iff.1 h1) hnP, fun h1 => absurd h1 hw1⟩
  have hψ := IVK.Lifted.ivk_Y_unique_of_II4 h44 hII G z S K₁ K₂ t u q w h hc Gs z' S' t' w' E₁ E₂ hmod hz'o
    hcenS' hdat hww
  obtain ⟨f, hf, hfS, hfP, hsurj, hfz⟩ :=
    exists_fhom_of_psi hX hPS hSO hzS hz1 hzc hz'2 hcenS' hψ
  have huP : u ∈ Pz S z := h.ch.u_mem
  have huS : u ∈ S := hPS huP
  have hu2 : u * u = 1 := (orderOf_two_iff.1 h.ch.u_ord).1
  have hu1 : u ≠ 1 := (orderOf_two_iff.1 h.ch.u_ord).2
  have hnc : ∀ g : G, ∃ s ∈ S, s * (g * u * g⁻¹) ≠ (g * u * g⁻¹) * s := by
    intro g
    by_contra hcon
    push Not at hcon
    set y : G := g * u * g⁻¹ with hy
    have hy2 : y * y = 1 := by
      calc y * y = g * (u * u) * g⁻¹ := by rw [hy]; group
        _ = 1 := by rw [hu2]; group
    have hy1 : y ≠ 1 := fun h1 => hu1 (conj_eq_one_iff.1 h1)
    have hycomm : ∀ s ∈ S, Commute y s := fun s hs => (hcon s hs).symm
    have hyS : y ∈ S := by
      have hpg : IsPGroup 2 ↥(zpowers y) := isPGroup_zpowers_of_sq hy2 hy1
      have hnorm : S ≤ normalizer (zpowers y : Set G) := by
        refine le_normalizer_of_commute (A := zpowers y) (B := S) ?_
        intro a ha b hb
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
        exact ((hycomm b hb).zpow_left k).eq
      have hQ : IsPGroup 2 ↥(S ⊔ zpowers y) := hSsyl.2.1.to_sup_of_normal_right' hpg hnorm
      have hQS : S ⊔ zpowers y = S := hSsyl.eq_of_le hQ le_sup_left le_top
      rw [← hQS]
      exact mem_sup_right (mem_zpowers y)
    have hfy : f y ∈ (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype := by
      refine ⟨⟨f y, hfS y hyS⟩, Subgroup.mem_center_iff.2 (fun gg => ?_), rfl⟩
      obtain ⟨s, hs, hsg⟩ := hsurj gg.1 gg.2
      apply Subtype.ext
      show (gg : Gs) * f y = f y * (gg : Gs)
      rw [← hsg, ← hf.mul s hs y hyS, ← hf.mul y hyS s hs, (hycomm s hs).eq.symm]
    rw [hcenS'] at hfy
    rcases (mem_zpowers_of_sq hz'2).1 hfy with h1 | h1
    · exact hy1 (hf.inj y hyS 1 S.one_mem (h1.trans hf.map_one.symm))
    · have hyz : y = z := hf.inj y hyS z hzS (h1.trans hfz.symm)
      have hconj : IsConj z u := isConj_iff.2 ⟨g⁻¹, by rw [← hyz, hy]; group⟩
      exact h.ch.u_ne (h.std.nonfused u huP hconj)
  obtain ⟨hA, hAcard⟩ := syl2In_inf_centralizer_of_index_two hSsyl hz2 hz1 hzc h.ch.u_norm hnc
  have hu'S' : f u ∈ (S' : Subgroup Gs) := hfS u huS
  have hu'E : f u ∈ IVK.Ez z' := hfP u huP
  have hu'o : orderOf (f u) = 2 := hf.orderOf_eq_two huS h.ch.u_ord
  have hu'ne : f u ≠ z' := fun e1 => h.ch.u_ne (hf.inj u huS z hzS (e1.trans hfz.symm))
  have hconj' : IsConj (t' * z') (f u) := hEfus (f u) hu'E hu'o hu'ne
  have hnc' : ¬ CFSG.GH74.IsCentralInvolution (f u) := fun hcu =>
    htzne ((hcentral (f u) hcu).trans hconj'.symm)
  have hnorm' : ∀ s' ∈ (S' : Subgroup Gs), s' * f u * s'⁻¹ = f u ∨ s' * f u * s'⁻¹ = f u * z' := by
    intro s' hs'
    obtain ⟨s, hs, rfl⟩ := hsurj s' hs'
    rw [← hf.map_conj hs huS]
    rcases h.ch.u_norm s hs with h1 | h1
    · left; rw [h1]
    · right; rw [h1, hf.mul u huS z hzS, hfz]
  have hex' : ∃ a ∈ (S' : Subgroup Gs), a * f u ≠ f u * a := by
    obtain ⟨s, hs, hne⟩ := hnc 1
    have hne' : s * u ≠ u * s := by simpa using hne
    refine ⟨f s, hfS s hs, fun h1 => hne' (hf.inj _ (S.mul_mem hs huS) _ (S.mul_mem huS hs) ?_)⟩
    rw [hf.mul s hs u huS, hf.mul u huS s hs]
    exact h1
  have hidx' := relIndex_inf_centralizer_eq_two hz'2 hz'1 hz'c hnorm' hex'
  have hcard' : 2 * Nat.card ↥((S' : Subgroup Gs) ⊓ centralizer ({f u} : Set Gs)) =
      Nat.card ↥(S' : Subgroup Gs) := by
    have h1 := Subgroup.relIndex_mul_card (H := (S' : Subgroup Gs) ⊓ centralizer ({f u} : Set Gs))
      (K := (S' : Subgroup Gs))
    rw [hidx', inf_eq_left.2 (inf_le_left : (S' : Subgroup Gs) ⊓ centralizer ({f u} : Set Gs) ≤
      (S' : Subgroup Gs))] at h1
    exact h1
  obtain ⟨D₁, D₂, n, hn, hsup, hcomm, hinf, hd1, hd2, hcen1, hu'D₁⟩ :=
    model_structure h412 h.ch.q_odd h.ch.q_ge hLU S' hu'o hnc' hcard'
  have hD₁S : ∀ d ∈ D₁, ∃ s ∈ S, f s = d := fun d hd =>
    hsurj d (((le_sup_left : D₁ ≤ D₁ ⊔ D₂).trans hsup.ge) hd).1
  have hD₂S : ∀ d ∈ D₂, ∃ s ∈ S, f s = d := fun d hd =>
    hsurj d (((le_sup_right : D₂ ≤ D₁ ⊔ D₂).trans hsup.ge) hd).1
  have hD₁A : D₁ ≤ (S' : Subgroup Gs) ⊓ centralizer ({f u} : Set Gs) := by
    rw [hsup]; exact le_sup_left
  have hD₂A : D₂ ≤ (S' : Subgroup Gs) ⊓ centralizer ({f u} : Set Gs) := by
    rw [hsup]; exact le_sup_right
  have hle : ∀ D : Subgroup Gs, D ≤ (S' : Subgroup Gs) ⊓ centralizer ({f u} : Set Gs) →
      pullback hf D ≤ S ⊓ centralizer ({u} : Set G) := by
    intro D hD g hg
    have hcen := Subgroup.mem_centralizer_singleton_iff.1 (hD hg.2).2
    refine ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact hf.inj _ (S.mul_mem hg.1 huS) _ (S.mul_mem huS hg.1)
      (by rw [hf.mul g hg.1 u huS, hf.mul u huS g hg.1]; exact hcen)
  have hcommV : ∀ a ∈ pullback hf D₁, ∀ b ∈ pullback hf D₂, a * b = b * a := by
    intro a ha b hb
    apply hf.inj _ (S.mul_mem ha.1 hb.1) _ (S.mul_mem hb.1 ha.1)
    rw [hf.mul a ha.1 b hb.1, hf.mul b hb.1 a ha.1]
    exact hcomm _ ha.2 _ hb.2
  have hinfV : pullback hf D₁ ⊓ pullback hf D₂ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : f g ∈ D₁ ⊓ D₂ := ⟨hg.1.2, hg.2.2⟩
    rw [hinf, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact hf.inj g hg.1.1 1 S.one_mem (h1.trans hf.map_one.symm)
  have hsupV : pullback hf D₁ ⊔ pullback hf D₂ = S ⊓ centralizer ({u} : Set G) := by
    apply le_antisymm (sup_le (hle D₁ hD₁A) (hle D₂ hD₂A))
    intro g hg
    have hfg : f g ∈ (S' : Subgroup Gs) ⊓ centralizer ({f u} : Set Gs) := by
      have hgu := Subgroup.mem_centralizer_singleton_iff.1 hg.2
      refine ⟨hfS g hg.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hf.mul g hg.1 u huS, ← hf.mul u huS g hg.1, hgu]
    rw [hsup] at hfg
    obtain ⟨d₁, hd₁, d₂, hd₂, hfd⟩ := mem_sup_of_commute hcomm hfg
    obtain ⟨s₁, hs₁, hfs₁⟩ := hD₁S d₁ hd₁
    obtain ⟨s₂, hs₂, hfs₂⟩ := hD₂S d₂ hd₂
    have hg12 : g = s₁ * s₂ := hf.inj g hg.1 _ (S.mul_mem hs₁ hs₂)
      (by rw [hf.mul s₁ hs₁ s₂ hs₂, hfs₁, hfs₂]; exact hfd)
    rw [hg12]
    exact mul_mem (mem_sup_left ⟨hs₁, hfs₁ ▸ hd₁⟩) (mem_sup_right ⟨hs₂, hfs₂ ▸ hd₂⟩)
  have huV₁ : u ∈ pullback hf D₁ := ⟨huS, hu'D₁⟩
  have hucomm : ∀ a ∈ pullback hf D₁, a * u = u * a := by
    intro a ha
    apply hf.inj _ (S.mul_mem ha.1 huS) _ (S.mul_mem huS ha.1)
    rw [hf.mul a ha.1 u huS, hf.mul u huS a ha.1]
    exact (hcen1 (f a) ha.2).symm
  have hux : IsConj u x := (h.ch.t_fus u huP h.ch.u_ord h.ch.u_ne).symm.trans hx
  obtain ⟨g, hg⟩ := isConj_iff.1 hux
  have hAx : Syl2In (cj (S ⊓ centralizer ({u} : Set G)) g⁻¹) (centralizer ({x} : Set G)) := by
    have := syl2In_cj hA g⁻¹
    rwa [cj_centralizer g⁻¹ u, inv_inv, hg] at this
  obtain ⟨c0, hc0, hcV⟩ := hAx.exists_conj hV
  rw [cj_cj] at hcV
  have hc0x : c0 * x = x * c0 := Subgroup.mem_centralizer_singleton_iff.1 hc0
  have hkx : (g⁻¹ * c0) * x * (g⁻¹ * c0)⁻¹ = u := by
    calc (g⁻¹ * c0) * x * (g⁻¹ * c0)⁻¹ = g⁻¹ * (c0 * x * c0⁻¹) * g := by group
      _ = g⁻¹ * x * g := by rw [hc0x]; group
      _ = u := by rw [← hg]; group
  set k : G := g⁻¹ * c0 with hk
  have hcjcomm : ∀ a ∈ cj (pullback hf D₁) k, ∀ b ∈ cj (pullback hf D₂) k, a * b = b * a := by
    intro a ha b hb
    have h1 : (k * a * k⁻¹) * (k * b * k⁻¹) = (k * b * k⁻¹) * (k * a * k⁻¹) := hcommV _ ha _ hb
    calc a * b = k⁻¹ * ((k * a * k⁻¹) * (k * b * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * b * k⁻¹) * (k * a * k⁻¹)) * k := by rw [h1]
      _ = b * a := by group
  refine ⟨cj (pullback hf D₁) k, cj (pullback hf D₂) k, n, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcV]; exact cj_mono ((hle D₁ hD₁A))
  · rw [hcV]; exact cj_mono ((hle D₂ hD₂A))
  · exact hcjcomm
  · rw [eq_bot_iff]
    intro y hy
    have h1 : k * y * k⁻¹ ∈ pullback hf D₁ ⊓ pullback hf D₂ := ⟨hy.1, hy.2⟩
    rw [hinfV, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact conj_eq_one_iff.1 h1
  · apply le_antisymm
    · exact sup_le (by rw [hcV]; exact cj_mono (hle D₁ hD₁A)) (by rw [hcV]; exact cj_mono (hle D₂ hD₂A))
    · intro y hy
      rw [hcV, mem_cj, ← hsupV] at hy
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcommV hy
      have hy' : y = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by
        calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
          _ = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by rw [hab]; group
      rw [hy']
      refine mul_mem (mem_sup_left ?_) (mem_sup_right ?_)
      · show k * (k⁻¹ * a * k) * k⁻¹ ∈ pullback hf D₁
        simpa [mul_assoc] using ha
      · show k * (k⁻¹ * b * k) * k⁻¹ ∈ pullback hf D₂
        simpa [mul_assoc] using hb
  · exact isDihedralTwoGroup_cj k (isDihedralTwoGroup_pullback hf hD₁S hd1)
  · exact isDihedralTwoGroup_cj k (isDihedralTwoGroup_pullback hf hD₂S hd2)
  · show k * x * k⁻¹ ∈ pullback hf D₁
    rw [hkx]
    exact huV₁
  · intro a ha
    have h1 : (k * a * k⁻¹) * u = u * (k * a * k⁻¹) := hucomm _ ha
    rw [← hkx] at h1
    calc a * x = k⁻¹ * ((k * a * k⁻¹) * (k * x * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * x * k⁻¹) * (k * a * k⁻¹)) * k := by rw [h1]
      _ = x * a := by group

end L79

end CFSG.GH74.GLS.Stage1.Main
