module

public import CFSG.ClassicalInvolution.Q3.Q3ZBLayer
public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3ZFrbInj

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3

section Unique

variable {G : Type} [Group G] [Finite G]

theorem CCore3.eq_of_mem_involution {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
    (c : CCore3 Ω K z) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hzL : z ∈ L) : L = K := by
  by_contra hLK
  obtain ⟨P, hP, hLP⟩ := c.exists_plane_of_ne hL hLK
  exact false_of_involution_mem_plane_member c.d (le_centralizingLayer hL) hzL
    c.hz.orderOf_eq_two hP hLP

theorem classical_eq_of_central {L : Subgroup G} {u w : G} (h : IsClassicalMember3 L u)
    (hw : IsCentralInvolution L w) : u = w := by
  obtain ⟨φ, hφ⟩ := h.exists_chart
  exact hφ.eq_of_central h.isCentralInvolution hw

end Unique

end CFSG.ClassicalInvolution.Q3.Q3Z

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
  CFSG.ClassicalInvolution.Q3.Q3ZA CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane form IsHyperbolicPlane
  isHyperbolicPlane_stdPlane longBlock planeGroup_stdPlane longInv)
open scoped MatrixGroups

theorem conjInvariant_conjClass3 {G : Type} [Group G] (K : Subgroup G) :
    ConjInvariant (conjClass3 K) := by
  rintro n L ⟨g, rfl⟩
  exact ⟨n * g, conjSub_mul n g K ▸ rfl⟩

structure IsHubLayer {G : Type} [Group G] (Ω : Set (Subgroup G)) (Kh : Subgroup G)
    (Λ : StatedSp 2 F3 →* G) : Prop where
  inj : Function.Injective Λ
  mem_hub : Kh ∈ Ω
  mem_plane : (planeGroup (stdPlane F3 2 0)).map Λ ∈ Ω
  comm : ∀ x ∈ Λ.range, ∀ k ∈ Kh, x * k = k * x

section HubLayer

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {Kh : Subgroup G} {Λ : StatedSp 2 F3 →* G}

theorem map_planeGroup_eq_conj (Λ : StatedSp 2 F3 →* G)
    {P : Submodule F3 (Fin 2 ⊕ Fin 2 → F3)} (hP : IsHyperbolicPlane P) :
    ∃ x ∈ Λ.range, (planeGroup P).map Λ =
      conjSub x ((planeGroup (stdPlane F3 2 0)).map Λ) := by
  obtain ⟨h, hh⟩ :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock
      hP (0 : Fin 2)
  refine ⟨Λ h, ⟨h, rfl⟩, ?_⟩
  rw [hh, Subgroup.map_map, planeGroup_stdPlane]
  show _ = (((longBlock F3 2 0).range).map Λ).map (MulAut.conj (Λ h)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp

theorem mem_of_mem_conjSub {S H : Subgroup G} (hH : H ≤ S) {y w : G} (hy : y ∈ S)
    (hw : w ∈ conjSub y H) : w ∈ S := by
  rw [mem_conjSub_iff] at hw
  have h1 := S.mul_mem (S.mul_mem hy (hH hw)) (S.inv_mem hy)
  simpa [mul_assoc] using h1

theorem plane0_le_range (Λ : StatedSp 2 F3 →* G) :
    (planeGroup (stdPlane F3 2 0)).map Λ ≤ Λ.range :=
  Subgroup.map_le_range _ _

theorem IsHubLayer.commutes_conj (hΛ : IsHubLayer Ω Kh Λ) {x : G} (hx : x ∈ Λ.range) :
    Commutes Kh (conjSub x ((planeGroup (stdPlane F3 2 0)).map Λ)) := by
  intro a ha b hb
  exact (hΛ.comm b (mem_of_mem_conjSub (plane0_le_range Λ) hx hb) a ha).symm

end HubLayer

section Hub

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {Kh : Subgroup G} {Λ : StatedSp 2 F3 →* G}


theorem IsHubLayer.exists_conj_of_commutes (hctx : Ctx G K z)
    (hΛ : IsHubLayer (conjClass3 K) Kh Λ) {L : Subgroup G} (hL : L ∈ conjClass3 K)
    (hc : Commutes Kh L) :
    ∃ x ∈ Λ.range, L = conjSub x ((planeGroup (stdPlane F3 2 0)).map Λ) := by
  obtain ⟨c⟩ := Ctx.nonempty_core hctx
  obtain ⟨l⟩ := c.nonempty_layer
  have hinj := l.injective (fun L ⟨g, hg⟩ => ⟨g, hg.symm⟩)
  obtain ⟨g, hg⟩ := hΛ.mem_hub
  set Λ' : StatedSp 2 F3 →* G := (MulAut.conj g).toMonoidHom.comp l.Θ with hΛ'
  have hΛ'inj : Function.Injective Λ' := (MulAut.conj g).injective.comp hinj
  have hA : ∀ L ∈ conjClass3 K, Commutes Kh L →
      ∃ P, IsHyperbolicPlane P ∧ L = (planeGroup P).map Λ' := by
    intro L hL hc
    rw [← hg] at hc
    exact exists_plane_of_commutes_conj l g hL hc
  have hB : Λ.range ≤ Λ'.range := by
    have htop : (Λ'.range).comap Λ = ⊤ := by
      refine eq_top_of_planeGroups_le (fun P hP x hx => ?_)
      obtain ⟨y, hy, hyeq⟩ := map_planeGroup_eq_conj Λ hP
      have hmem : conjSub y ((planeGroup (stdPlane F3 2 0)).map Λ) ∈ conjClass3 K :=
        conjInvariant_conjClass3 K y _ hΛ.mem_plane
      obtain ⟨P', hP', hLP'⟩ := hA _ hmem (hΛ.commutes_conj hy)
      have hx' : Λ x ∈ (planeGroup P).map Λ := ⟨x, hx, rfl⟩
      rw [hyeq, hLP'] at hx'
      obtain ⟨w, -, hw⟩ := hx'
      exact ⟨w, hw⟩
    rintro _ ⟨x, rfl⟩
    have : x ∈ (Λ'.range).comap Λ := by rw [htop]; trivial
    exact this
  have hcard₁ : Nat.card Λ'.range = Nat.card (StatedSp 2 F3) :=
    (Nat.card_congr (MonoidHom.ofInjective hΛ'inj).toEquiv).symm
  have hcard₂ : Nat.card Λ.range = Nat.card (StatedSp 2 F3) :=
    (Nat.card_congr (MonoidHom.ofInjective hΛ.inj).toEquiv).symm
  have heq : Λ.range = Λ'.range :=
    Subgroup.eq_of_le_of_card_ge hB (by rw [hcard₁, hcard₂])
  obtain ⟨P, hP, hLP⟩ := hA L hL hc
  have hK₀c : Commutes Kh ((planeGroup (stdPlane F3 2 0)).map Λ) := fun a ha b hb =>
    (hΛ.comm b (plane0_le_range Λ hb) a ha).symm
  obtain ⟨P₀, hP₀, hK₀P₀⟩ := hA _ hΛ.mem_plane hK₀c
  obtain ⟨h, hh⟩ := Q3Z.exists_conj_planeGroup (F := F3) (n := 2) (by norm_num) hP₀ hP
  refine ⟨Λ' h, ?_, ?_⟩
  · rw [heq]
    exact ⟨h, rfl⟩
  · rw [hLP, hh, hK₀P₀, Subgroup.map_map]
    show _ = ((planeGroup P₀).map Λ').map (MulAut.conj (Λ' h)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp

theorem IsHubLayer.conj_mem_range (hctx : Ctx G K z) (hΛ : IsHubLayer (conjClass3 K) Kh Λ)
    {g : G} (hg : conjSub g Kh = Kh) (s : StatedSp 2 F3) : g * Λ s * g⁻¹ ∈ Λ.range := by
  have htop : (Λ.range).comap ((MulAut.conj g).toMonoidHom.comp Λ) = ⊤ := by
    refine eq_top_of_planeGroups_le (fun P hP x hx => ?_)
    obtain ⟨y, hy, hyeq⟩ := map_planeGroup_eq_conj Λ hP
    have hmem : conjSub g (conjSub y ((planeGroup (stdPlane F3 2 0)).map Λ)) ∈ conjClass3 K :=
      conjInvariant_conjClass3 K g _ (conjInvariant_conjClass3 K y _ hΛ.mem_plane)
    have hcm : Commutes Kh (conjSub g (conjSub y ((planeGroup (stdPlane F3 2 0)).map Λ))) := by
      have := (commutes_conjSub_iff (K := Kh) (L := conjSub y
        ((planeGroup (stdPlane F3 2 0)).map Λ)) g).2 (hΛ.commutes_conj hy)
      rwa [hg] at this
    obtain ⟨y', hy', hy'eq⟩ := hΛ.exists_conj_of_commutes hctx hmem hcm
    have hx' : g * Λ x * g⁻¹ ∈ conjSub g ((planeGroup P).map Λ) :=
      ⟨Λ x, ⟨x, hx, rfl⟩, rfl⟩
    rw [hyeq, hy'eq] at hx'
    exact mem_of_mem_conjSub (plane0_le_range Λ) hy' hx'
  have : s ∈ (Λ.range).comap ((MulAut.conj g).toMonoidHom.comp Λ) := by rw [htop]; trivial
  exact this

theorem conjSub_eq_of_centralizes (hctx : Ctx G K z) {M : Subgroup G} (hM : M ∈ conjClass3 K)
    {w : G} (hw : IsCentralInvolution M w) {g : G} (hg : g * w = w * g) : conjSub g M = M := by
  obtain ⟨b, hb⟩ := hM
  have hzb : IsClassicalMember3 M (b * z * b⁻¹) := hb ▸ hctx.setup.cls.conj b
  have hwz : b * z * b⁻¹ = w := classical_eq_of_central hzb hw
  obtain ⟨c⟩ := Ctx.nonempty_core hctx
  have hg' : (b⁻¹ * g * b) * z = z * (b⁻¹ * g * b) := by
    have h1 : g * (b * z * b⁻¹) = (b * z * b⁻¹) * g := by rw [hwz]; exact hg
    calc (b⁻¹ * g * b) * z = b⁻¹ * (g * (b * z * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * z * b⁻¹) * g) * b := by rw [h1]
      _ = z * (b⁻¹ * g * b) := by group
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hctx.setup.cls.subnormal
  have hL : conjSub (b⁻¹ * g * b) K ∈ centralizingMembers (conjClass3 K) {z} := by
    refine ⟨conjInvariant_conjClass3 K _ K ⟨1, conjSub_one K⟩, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    have hk' := Subgroup.mem_centralizer_singleton_iff.1 (hKz hk)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (b⁻¹ * g * b) * k * (b⁻¹ * g * b)⁻¹ * z = z * ((b⁻¹ * g * b) * k * (b⁻¹ * g * b)⁻¹)
    calc (b⁻¹ * g * b) * k * (b⁻¹ * g * b)⁻¹ * z
        = (b⁻¹ * g * b) * (k * ((b⁻¹ * g * b)⁻¹ * z * (b⁻¹ * g * b))) * (b⁻¹ * g * b)⁻¹ := by
          group
      _ = (b⁻¹ * g * b) * (k * z) * (b⁻¹ * g * b)⁻¹ := by
          rw [show (b⁻¹ * g * b)⁻¹ * z * (b⁻¹ * g * b) = z by
            rw [mul_assoc, ← hg', ← mul_assoc, inv_mul_cancel, one_mul]]
      _ = (b⁻¹ * g * b) * (z * k) * (b⁻¹ * g * b)⁻¹ := by rw [hk']
      _ = z * ((b⁻¹ * g * b) * k * (b⁻¹ * g * b)⁻¹) := by
          rw [show (b⁻¹ * g * b) * (z * k) * (b⁻¹ * g * b)⁻¹
            = ((b⁻¹ * g * b) * z * (b⁻¹ * g * b)⁻¹) * ((b⁻¹ * g * b) * k * (b⁻¹ * g * b)⁻¹) by
              group, show (b⁻¹ * g * b) * z * (b⁻¹ * g * b)⁻¹ = z by
              rw [hg', mul_assoc, mul_inv_cancel, mul_one]]
  have hzL : z ∈ conjSub (b⁻¹ * g * b) K := by
    refine ⟨z, c.hz.mem, ?_⟩
    show (b⁻¹ * g * b) * z * (b⁻¹ * g * b)⁻¹ = z
    rw [hg', mul_assoc, mul_inv_cancel, mul_one]
  have hLK := c.eq_of_mem_involution hL hzL
  rw [← hb]
  calc conjSub g (conjSub b K) = conjSub b (conjSub (b⁻¹ * g * b) K) := by
        rw [← conjSub_mul, ← conjSub_mul]; congr 1; group
    _ = conjSub b K := by rw [hLK]

theorem layers_sup_eq_top_of_hub (hctx : Ctx G K z) {Kp : Subgroup G} {A X : StatedSp 2 F3 →* G}
    (hX : IsHubLayer (conjClass3 K) Kh X) (hXp : (planeGroup (stdPlane F3 2 0)).map X = Kp)
    (hA0 : (planeGroup (stdPlane F3 2 0)).map A = Kp)
    (hA1 : (planeGroup (stdPlane F3 2 1)).map A = Kh) : A.range ⊔ X.range = ⊤ := by
  set M := A.range ⊔ X.range with hM
  have hconn : RouteD.DeltaConnected (conjClass3 K) :=
    (CoreAssembly.deltaConnected_iff K).mp hctx.setup.conn
  obtain ⟨g, hg⟩ := Q3Z.exists_conj_planeGroup (F := F3) (n := 2) (by norm_num)
    (isHyperbolicPlane_stdPlane 1) (isHyperbolicPlane_stdPlane 0)
  have hKpeq : Kp = conjSub (A g) Kh := by
    rw [← hA0, ← hA1, hg, Subgroup.map_map]
    show _ = ((planeGroup (stdPlane F3 2 1)).map A).map (MulAut.conj (A g)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp
  let 𝔖 : Set (Subgroup G) := {L | L ∈ conjClass3 K ∧ ∃ m ∈ M, L = conjSub m Kh}
  have hcover : conjClass3 K ⊆ 𝔖 := by
    refine subset_of_adj_closed hconn (fun L hL => hL.1)
      ⟨Kh, hX.mem_hub, 1, M.one_mem, (conjSub_one _).symm⟩ ?_
    rintro N ⟨hN, m, hm, rfl⟩ L hL hLN hc
    have hL' : conjSub m⁻¹ L ∈ conjClass3 K := conjInvariant_conjClass3 K m⁻¹ L hL
    have hc' : Commutes Kh (conjSub m⁻¹ L) := by
      have := (commutes_conjSub_iff (K := conjSub m Kh) (L := L) m⁻¹).2 hc
      rwa [conjSub_inv_conjSub] at this
    obtain ⟨x, hx, hxeq⟩ := hX.exists_conj_of_commutes hctx hL' hc'
    refine ⟨hL, m * x * A g, ?_, ?_⟩
    · exact M.mul_mem (M.mul_mem hm (Subgroup.mem_sup_right hx))
        (Subgroup.mem_sup_left ⟨g, rfl⟩)
    · calc L = conjSub m (conjSub m⁻¹ L) := (conjSub_conjSub_inv m L).symm
        _ = conjSub m (conjSub x Kp) := by rw [hxeq, hXp]
        _ = conjSub (m * x * A g) Kh := by rw [hKpeq, ← conjSub_mul, ← conjSub_mul]
  have hKh1 : Kh ≤ M := by
    rw [← hA1]
    exact (Subgroup.map_le_range _ _).trans le_sup_left
  have hmem : ∀ L ∈ conjClass3 K, L ≤ M := by
    intro L hL
    obtain ⟨-, m, hm, rfl⟩ := hcover hL
    rintro _ ⟨k, hk, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hKh1 hk)) (M.inv_mem hm)
  have hK : K ≠ ⊥ := by
    intro h
    have hz : z ∈ K := hctx.setup.cls.mem
    rw [h, Subgroup.mem_bot] at hz
    have := hctx.setup.cls.orderOf_eq_two
    rw [hz, orderOf_one] at this
    omega
  have hnc : Subgroup.normalClosure (K : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure (K : Set G)) with h | h
    · exact absurd (le_bot_iff.1 (Subgroup.le_normalClosure.trans h.le)) hK
    · exact h
  have hle : Subgroup.normalClosure (K : Set G) ≤ M := by
    show Subgroup.closure (Group.conjugatesOfSet _) ≤ M
    rw [Subgroup.closure_le]
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hcj⟩ := hx
    obtain ⟨g, rfl⟩ := isConj_iff.1 hcj
    exact hmem (conjSub g K) ⟨g, rfl⟩ (conj_mem_conjSub ha)
  exact eq_top_iff.2 (hnc ▸ hle)

theorem eq_one_of_centralizes_layers (hctx : Ctx G K z) {Kp : Subgroup G}
    {A X : StatedSp 2 F3 →* G} (hX : IsHubLayer (conjClass3 K) Kh X)
    (hXp : (planeGroup (stdPlane F3 2 0)).map X = Kp)
    (hA0 : (planeGroup (stdPlane F3 2 0)).map A = Kp)
    (hA1 : (planeGroup (stdPlane F3 2 1)).map A = Kh) {s : G}
    (h₁ : ∀ y ∈ A.range, y * s = s * y) (h₂ : ∀ y ∈ X.range, y * s = s * y) : s = 1 := by
  have hs : s ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ A.range ⊔ X.range := by
      rw [layers_sup_eq_top_of_hub hctx hX hXp hA0 hA1]; trivial
    have hle : A.range ⊔ X.range ≤ Subgroup.centralizer {s} := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (h₁ y hy).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (h₂ y hy).symm
    have := Subgroup.mem_centralizer_iff.1 (hle hg) s (Set.mem_singleton s)
    exact this.symm
  have hcen : Subgroup.center G = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot G hctx.nab
  rw [hcen, Subgroup.mem_bot] at hs
  exact hs

end Hub

end CFSG.ClassicalInvolution.Q3.Q3ZB
