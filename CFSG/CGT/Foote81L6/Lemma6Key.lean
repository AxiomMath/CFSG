module

public import CFSG.CGT.Foote81L6.NBar
public import CFSG.CGT.Foote81L6.E64Fix
public import CFSG.CGT.Foote81L6.Normalizer.Lemma6Core
public import CFSG.CGT.Foote81L6.DescentCore

public section

namespace CFSG.CGT.Foote81L6

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative

theorem exists_normalizer_conj {G : Type*} [Group G] [Finite G] {T S F : Subgroup G} {e x : G}
    (SK : Sylow 2 ↥(centralizer ({e} : Set G)))
    (hSK : (SK : Subgroup _) = S.subgroupOf (centralizer ({e} : Set G))) (hST : S ≤ T)
    (hF2 : IsPGroup 2 F) (hFc : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u) (hxe : x * e * x⁻¹ ∈ F)
    (hL5 : ∀ g : G, F.map (MulAut.conj g).toMonoidHom ≤ T →
      ∃ h ∈ T, F.map (MulAut.conj g).toMonoidHom = F.map (MulAut.conj h).toMonoidHom) :
    ∃ n ∈ normalizer (F : Set G), ∃ h ∈ T, h⁻¹ * e * h ∈ F ∧
      n * (h⁻¹ * e * h) * n⁻¹ = x * e * x⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ k y : G, (MulAut.conj k).toMonoidHom y = k * y * k⁻¹ := fun k y => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  set P : Subgroup G := F.map (MulAut.conj x⁻¹).toMonoidHom
  have hPK : P ≤ centralizer ({e} : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff, hconj, inv_inv]
    have h := hFc _ hxe v hv
    calc x⁻¹ * v * x * e = x⁻¹ * (v * (x * e * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * e * x⁻¹) * v) * x := by rw [h]
      _ = e * (x⁻¹ * v * x) := by group
  have hP2 : IsPGroup 2 (P.subgroupOf (centralizer ({e} : Set G))) := (hF2.map _).comap_subtype
  obtain ⟨c, hc⟩ := exists_conj_mem_of_isPGroup SK hP2
  have hce : (c : G) * e = e * c := mem_centralizer_singleton_iff.1 c.2
  set g : G := (c : G) * x⁻¹
  have hgT : F.map (MulAut.conj g).toMonoidHom ≤ T := by
    rintro _ ⟨v, hv, rfl⟩
    have hvP : x⁻¹ * v * x ∈ P := ⟨v, hv, by rw [hconj, inv_inv]⟩
    have hy : (⟨x⁻¹ * v * x, hPK hvP⟩ : centralizer ({e} : Set G)) ∈
        P.subgroupOf (centralizer ({e} : Set G)) := by
      rw [mem_subgroupOf]
      exact hvP
    have h1 := hc _ hy
    rw [hSK, mem_subgroupOf] at h1
    apply hST
    rw [hconj]
    convert h1 using 1
    simp only [g, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  obtain ⟨h, hhT, hFh⟩ := hL5 g hgT
  have hmem : ∀ {k y : G}, y ∈ F.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * y * k ∈ F := by
    intro k y
    rw [mem_map_equiv, MulAut.conj_symm_apply]
  refine ⟨x * (c : G)⁻¹ * h, ?_, h, hhT, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro v
    have e1 : v ∈ F ↔ h * v * h⁻¹ ∈ F.map (MulAut.conj h).toMonoidHom := by
      rw [hmem]; group
    rw [e1, ← hFh, hmem]
    constructor <;> intro hv <;> convert hv using 1 <;> simp only [g] <;> group
  · have : e ∈ F.map (MulAut.conj g).toMonoidHom := by
      rw [hmem]
      convert hxe using 1
      simp only [g]
      calc ((c : G) * x⁻¹)⁻¹ * e * ((c : G) * x⁻¹) = x * ((c : G)⁻¹ * (e * c)) * x⁻¹ := by group
        _ = x * e * x⁻¹ := by rw [← hce]; group
    rw [hFh, hmem] at this
    exact this
  · calc x * (c : G)⁻¹ * h * (h⁻¹ * e * h) * (x * (c : G)⁻¹ * h)⁻¹
        = x * ((c : G)⁻¹ * (e * c)) * x⁻¹ := by group
      _ = x * e * x⁻¹ := by rw [← hce]; group

namespace FooteCore

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {k n : ℕ}
  (D : FooteCore G (T : Subgroup G) (k + 3) n)

private theorem π_eq_of_mul_inv_mem {F : Subgroup G} (hFc : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u)
    (y : ↥(normalizer (F : Set G))) {β : G} (hyβ : (y : G) * β⁻¹ ∈ F) :
    ∃ hβ : β ∈ normalizer (F : Set G), NBar.π F y = NBar.π F ⟨β, hβ⟩ := by
  have hβN : β ∈ normalizer (F : Set G) := by
    have : β = ((y : G) * β⁻¹)⁻¹ * y := by group
    rw [this]
    exact mul_mem (inv_mem (le_normalizer hyβ)) y.2
  refine ⟨hβN, ?_⟩
  rw [NBar.π_eq_π_iff]
  intro v hv
  have hβv : β * v * β⁻¹ ∈ F := (mem_normalizer_iff.1 hβN v).1 hv
  calc (y : G) * v * (y : G)⁻¹ = ((y : G) * β⁻¹) * (β * v * β⁻¹) * ((y : G) * β⁻¹)⁻¹ := by group
    _ = β * v * β⁻¹ := by rw [hFc _ hyβ _ hβv]; group

private theorem mem_normalizer_inf {F X : Subgroup G} {β : G} (hβX : β ∈ X)
    (hβN : β ∈ normalizer (F : Set G)) : β ∈ normalizer ((F ⊓ X : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  rw [mem_inf, mem_inf, ← (mem_normalizer_iff.1 hβN h)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, mul_mem (mul_mem hβX h2) (inv_mem hβX)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : h = β⁻¹ * (β * h * β⁻¹) * β := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hβX) h2) hβX

theorem lemma6Key_core (P : Subgroup G → Prop)
    (hL3 : ∀ y ∈ D.Zab, IsConj D.a y → y = D.a)
    (hSylN : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∃ Q : Sylow 2 ↥(normalizer (E : Set G)),
      (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (E : Set G)))
    (hTv : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∀ x c : G, x ∈ (T : Subgroup G) →
      x ∈ normalizer (E : Set G) → (∀ v ∈ E, x * v * x⁻¹ = v ∨ x * v * x⁻¹ = v * c) →
      (∃ v ∈ E, x * v * x⁻¹ ≠ v) →
      (∃ α ∈ D.A, x * α⁻¹ ∈ E) ∨ (∃ β ∈ D.B₀, x * β⁻¹ ∈ E) ∨ (∃ β ∈ D.B₁, x * β⁻¹ ∈ E))
    (hS : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → P E →
      ∃ s' ∈ D.B ⊓ normalizer (E : Set G), D.B₀.map (MulAut.conj s').toMonoidHom = D.B₁)
    (hP : ∀ x ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), x * x = 1 →
      ∃ E : Subgroup G, IsE64 (T : Subgroup G) E ∧ P E ∧ x ∈ E)
    {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F) {x : G} (hxN : x ∈ normalizer (F : Set G))
    (hxF : x * D.a * x⁻¹ ∈ F) (hxA : x * D.a * x⁻¹ ∉ D.A) :
    (∃ x' : G, ∃ F' : Subgroup G, IsE64 (T : Subgroup G) F' ∧ P F' ∧ x' * D.a * x'⁻¹ ∈ F' ∧
      x' * D.a * x'⁻¹ ∉ D.A) ∧
    (P F → ∃ y : G, ∃ a₁ ∈ D.A, orderOf a₁ = 2 ∧ a₁ ≠ D.a ∧ y * D.a * y⁻¹ = a₁ * D.b ∧
      y * D.b * y⁻¹ = D.b) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : 3 ≤ k + 3 := by omega
  have hF2 := hF.mul_self
  have hFc : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u := fun u hu v hv =>
    TStruct.comm_of_mul_self hF2 hu hv
  haveI : IsMulCommutative ↥F := ⟨⟨fun u v => Subtype.ext (hFc _ u.2 _ v.2)⟩⟩
  haveI : Finite ↥F := hF.finite
  have hV : ∀ v : ↥F, v * v = 1 := fun v => Subtype.ext (hF2 v v.2)
  have haF : D.a ∈ F := D.a_mem_E64 hF
  have hb₀F : D.b₀ ∈ F := D.b₀_mem_E64 hF
  have hb₁F : D.b₁ ∈ F := D.b₁_mem_E64 hF
  set w : ↥F := ⟨D.a, haF⟩ with hw_def
  have hw1 : w ≠ 1 := fun h => D.a_ne_one (congrArg Subtype.val h)
  obtain ⟨Q, hQ⟩ := hSylN F hF
  have hmemQ : ∀ y : ↥(normalizer (F : Set G)), y ∈ Q ↔ (y : G) ∈ (T : Subgroup G) := by
    intro y
    show y ∈ (Q : Subgroup _) ↔ _
    rw [hQ, mem_subgroupOf]
  have hρne : ∀ y : ↥(normalizer (F : Set G)), (y : G) ∈ (T : Subgroup G) → (y : G) ∉ F →
      NBar.ρ F (NBar.π F y) ≠ 1 := by
    intro y hyT hyF h
    apply hyF
    have h1 : NBar.π F y = 1 := NBar.ρ_injective F (h.trans (map_one _).symm)
    rw [NBar.π_eq_one_iff] at h1
    have hmem : (y : G) ∈ (T : Subgroup G) ⊓ centralizer (F : Set G) := by
      refine mem_inf.2 ⟨hyT, mem_centralizer_iff.2 fun v hv => ?_⟩
      calc v * y = ((y : G) * v * (y : G)⁻¹) * y := by rw [h1 v hv]
        _ = y * v := by group
    rw [D.centralizer_E64 hF] at hmem
    exact hmem
  obtain ⟨d, hdR, -, hdF, hdN, hdc⟩ := D.exists_d hm hF
  have hdA : d ∈ D.A := (mem_inf.1 hdR).1
  have hdT : d ∈ (T : Subgroup G) := D.A_le_T hdA
  set dN : ↥(normalizer (F : Set G)) := ⟨d, hdN⟩
  set dbar := NBar.π F dN
  have htv : IsTransvectionWith (NBar.ρ F dbar) w :=
    NBar.isTransvectionWith_of_commutator F dN haF D.a_ne_one D.a_mul_a hdc.le
  have hd1 : NBar.ρ F dbar ≠ 1 := hρne dN hdT hdF
  set Dbar := NBar.sylowImage F Q
  have hdD : dbar ∈ (Dbar : Subgroup (NBar.Q F)) := by
    rw [NBar.coe_sylowImage]
    exact ⟨dN, (hmemQ dN).2 hdT, rfl⟩
  have hfus : ∀ yb ∈ (Dbar : Subgroup (NBar.Q F)), IsConj dbar yb → yb = dbar := by
    intro yb hyb' hconj
    rw [NBar.coe_sylowImage] at hyb'
    obtain ⟨yN, hyQ, rfl⟩ := hyb'
    have hyT : (yN : G) ∈ (T : Subgroup G) := (hmemQ yN).1 hyQ
    obtain ⟨gbar, hg⟩ := isConj_iff.1 hconj
    obtain ⟨gN, rfl⟩ := NBar.π_surjective F gbar
    have hρy : NBar.ρ F (NBar.π F yN) =
        NBar.ρ F (NBar.π F gN) * NBar.ρ F dbar * (NBar.ρ F (NBar.π F gN))⁻¹ := by
      rw [← hg, map_mul, map_mul, map_inv]
    have htvy : IsTransvectionWith (NBar.ρ F (NBar.π F yN)) (NBar.ρ F (NBar.π F gN) w) :=
      hρy ▸ B1.tv_conj htv _
    have hy1 : NBar.ρ F (NBar.π F yN) ≠ 1 := hρy ▸ B1.tv_conj_ne_one hd1 _
    have hcval : ((NBar.ρ F (NBar.π F gN) w : ↥F) : G) = gN * D.a * (gN : G)⁻¹ :=
      NBar.ρ_π F gN w
    have htvG : ∀ v ∈ F, (yN : G) * v * (yN : G)⁻¹ = v ∨
        (yN : G) * v * (yN : G)⁻¹ = v * ((NBar.ρ F (NBar.π F gN) w : ↥F) : G) := by
      intro v hv
      rcases htvy.2 ⟨v, hv⟩ with h | h
      · left
        have := congrArg Subtype.val h
        rwa [NBar.ρ_π] at this
      · right
        have := congrArg Subtype.val h
        rwa [NBar.ρ_π] at this
    have hmoveG : ∃ v ∈ F, (yN : G) * v * (yN : G)⁻¹ ≠ v := by
      obtain ⟨v, hv⟩ := B1.exists_moved_of_ne_one hy1
      exact ⟨v, v.2, fun h => hv (Subtype.ext (by rw [NBar.ρ_π]; exact h))⟩
    have hBcase : ∀ (X : Subgroup G) (bX : G) (hbX : bX ∈ F), bX ∈ D.B → bX ∈ D.Zab →
        bX ≠ 1 → bX * bX = 1 → ∀ β ∈ X, (yN : G) * β⁻¹ ∈ F →
        (β ∈ X ⊓ normalizer ((F ⊓ X : Subgroup G) : Set G) → β ∉ F →
          ⁅F, zpowers β⁆ = zpowers bX) → False := by
      intro X bX hbX hbXB hbXZ hbX1 hbX2 β hβX hyβ hcomm
      obtain ⟨hβN, hπβ⟩ := π_eq_of_mul_inv_mem hFc yN hyβ
      have hβF : β ∉ F := by
        intro h
        apply hy1
        rw [hπβ, NBar.π_eq_one_of_mem F hFc _ h, map_one]
      have hc := hcomm (mem_inf.2 ⟨hβX, mem_normalizer_inf hβX hβN⟩) hβF
      have htvβ : IsTransvectionWith (NBar.ρ F (NBar.π F ⟨β, hβN⟩)) ⟨bX, hbX⟩ :=
        NBar.isTransvectionWith_of_commutator F ⟨β, hβN⟩ hbX hbX1 hbX2 hc.le
      rw [← hπβ] at htvβ
      have heq := NBar.eq_of_isTransvectionWith htvy htvβ hy1
      have hconjb : (gN : G) * D.a * (gN : G)⁻¹ = bX := by
        rw [← hcval]
        exact congrArg Subtype.val heq
      have hba := hL3 bX hbXZ (isConj_iff.2 ⟨gN, hconjb⟩)
      rw [hba] at hbXB
      exact D.a_not_mem_B hbXB
    have hb₀Z : D.b₀ ∈ D.Zab := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hb₁Z : D.b₁ ∈ D.Zab :=
      subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    rcases hTv F hF yN _ hyT yN.2 htvG hmoveG with ⟨α, hα, hyα⟩ | ⟨β, hβ, hyβ⟩ | ⟨β, hβ, hyβ⟩
    ·
      obtain ⟨hαN, hπα⟩ := π_eq_of_mul_inv_mem hFc yN hyα
      have hαF : α ∉ F := by
        intro h
        apply hy1
        rw [hπα, NBar.π_eq_one_of_mem F hFc _ h, map_one]
      have hαR : α ∈ D.A ⊓ normalizer ((F ⊓ D.A : Subgroup G) : Set G) :=
        mem_inf.2 ⟨hα, mem_normalizer_inf hα hαN⟩
      have hFAR : F ⊓ D.A ≤ D.A ⊓ normalizer ((F ⊓ D.A : Subgroup G) : Set G) :=
        le_inf inf_le_right le_normalizer
      have hαd := inv_mul_mem_of_card_eq_two_mul hFAR
        (by rw [D.card_R hm hF, (D.E64_decomp hF).2.1.2.2]) hαR hdR
        (fun h => hαF (mem_inf.1 h).1) (fun h => hdF (mem_inf.1 h).1)
      have hπd : NBar.π F ⟨α, hαN⟩ = dbar := by
        rw [NBar.π_eq_π_iff]
        intro v hv
        have hc : (α⁻¹ * d) * v = v * (α⁻¹ * d) := hFc _ (mem_inf.1 hαd).1 _ hv
        calc α * v * α⁻¹ = α * ((α⁻¹ * d) * v * (α⁻¹ * d)⁻¹) * α⁻¹ := by rw [hc]; group
          _ = d * v * d⁻¹ := by group
      rw [hπα, hπd]
    · exact (hBcase D.B₀ D.b₀ hb₀F D.b₀_mem_B hb₀Z D.b₀_ne_one D.b₀_mul_b₀ β hβ hyβ
        fun hβR hβF => D.commutator_E64_B₀ hF hβR hβF).elim
    · exact (hBcase D.B₁ D.b₁ hb₁F D.b₁_mem_B hb₁Z D.b₁_ne_one D.b₁_mul_b₁ β hβ hyβ
        fun hβR hβF => D.commutator_E64_B₁ hF hβR hβF).elim
  have hmove : ∃ g : NBar.Q F, NBar.ρ F g w ≠ w := by
    refine ⟨NBar.π F ⟨x, hxN⟩, fun h => hxA ?_⟩
    have h' := congrArg Subtype.val h
    rw [NBar.ρ_π] at h'
    have h'' : x * D.a * x⁻¹ = D.a := h'
    rw [h'']
    exact D.a_mem
  obtain ⟨ybar, hyb⟩ := Normalizer.exists_isolatedTransvectionBlock hV (NBar.ρ_injective F) Dbar
    hdD htv hd1 hfus hmove
  set Y := commV (zpowers (NBar.ρ F ybar)) with hY_def
  set u : ↥F := NBar.ρ F ybar w with hu_def
  set u' : ↥F := NBar.ρ F ybar u with hu'_def
  have hcard : Nat.card ↥Y = 4 := hyb.card_comm
  have hwY : w ∈ Y := hyb.centre_mem
  have hmc : ∀ v ∈ Y, v = 1 ∨ v = w ∨ v = u ∨ v = u' := hyb.mem_comm
  have hinv : ∀ g : NBar.Q F, ∀ v ∈ Y, NBar.ρ F g v ∈ Y := hyb.comm_invariant
  have huY : u ∈ Y := hinv ybar w hwY
  have hu1 : u ≠ 1 := by
    intro h
    apply hw1
    apply (NBar.ρ F ybar).injective
    rw [map_one]
    exact h
  have huw : u ≠ w := by
    intro h
    have hu' : u' = w := by
      show NBar.ρ F ybar u = w
      rw [h]
      exact h
    have hsub : (Y : Set ↥F) ⊆ {1, w} := by
      intro v hv
      rcases hmc v hv with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact Or.inr (h1.trans h)
      · exact Or.inr (h1.trans hu')
    have hle : Nat.card ↥Y ≤ 2 := by
      have e : Nat.card ↥Y = (Y : Set ↥F).ncard := Nat.card_coe_set_eq _
      rw [e]
      calc (Y : Set ↥F).ncard ≤ ({1, w} : Set ↥F).ncard := Set.ncard_le_ncard hsub
        _ ≤ ({w} : Set ↥F).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  have hwu : w * u = u' := by
    rcases hmc _ (mul_mem hwY huY) with h1 | h1 | h1 | h1
    · exfalso
      apply huw
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right (hV w)]
    · exfalso
      exact hu1 (mul_left_cancel (h1.trans (mul_one w).symm))
    · exfalso
      exact hw1 (mul_right_cancel (h1.trans (one_mul u).symm))
    · exact h1
  have huu' : u ≠ u' := by
    intro h
    apply huw
    apply (NBar.ρ F ybar).injective
    exact h.symm
  have huA : (u : G) ∉ D.A := by
    intro huA
    have hxY : NBar.ρ F (NBar.π F ⟨x, hxN⟩) w ∈ Y := hinv _ w hwY
    have hxval : ((NBar.ρ F (NBar.π F ⟨x, hxN⟩) w : ↥F) : G) = x * D.a * x⁻¹ :=
      NBar.ρ_π F _ w
    rcases hmc _ hxY with h1 | h1 | h1 | h1 <;> rw [h1] at hxval
    · rw [OneMemClass.coe_one] at hxval
      exact D.a_ne_one (conj_eq_one_iff.1 hxval.symm)
    · apply hxA
      rw [← hxval]
      exact D.a_mem
    · apply hxA
      rw [← hxval]
      exact huA
    · apply hxA
      rw [← hxval, ← hwu]
      exact mul_mem D.a_mem huA
  have h3 : ybar ^ 3 = 1 := by rw [← hyb.orderOf_eq]; exact pow_orderOf_eq_one ybar
  have hconj_cases : ∀ g : NBar.Q F, g * ybar * g⁻¹ = ybar ∨ g * ybar * g⁻¹ = ybar * ybar := by
    intro g
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hyb.normal.conj_mem ybar (mem_zpowers ybar) g)
    rw [zpow_eq_zpow_emod' j h3, show ((3 : ℕ) : ℤ) = 3 from rfl] at hj
    have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hj3 with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hj
      have hy1 : ybar = 1 := conj_eq_one_iff.1 hj.symm
      have := hyb.orderOf_eq
      rw [hy1, orderOf_one] at this
      omega
    · left
      rw [h1, zpow_one] at hj
      exact hj.symm
    · right
      rw [h2, zpow_two] at hj
      exact hj.symm
  have hcent : ∀ βN : ↥(normalizer (F : Set G)), (βN : G) ∈ D.B → ∀ c : ↥F, (c : G) ∈ D.B →
      IsTransvectionWith (NBar.ρ F (NBar.π F βN)) c →
      NBar.π F βN * ybar = ybar * NBar.π F βN := by
    intro βN hβB c hcB htvc
    have hβw : NBar.ρ F (NBar.π F βN) w = w := by
      apply Subtype.ext
      rw [NBar.ρ_π]
      show (βN : G) * D.a * (βN : G)⁻¹ = D.a
      rw [← D.A_comm_B D.a D.a_mem _ hβB, mul_inv_cancel_right]
    rcases hconj_cases (NBar.π F βN) with h | h
    · calc NBar.π F βN * ybar = NBar.π F βN * ybar * (NBar.π F βN)⁻¹ * NBar.π F βN := by group
        _ = ybar * NBar.π F βN := by rw [h]
    · exfalso
      have hβy : NBar.π F βN * ybar = ybar * ybar * NBar.π F βN := by
        calc NBar.π F βN * ybar = NBar.π F βN * ybar * (NBar.π F βN)⁻¹ * NBar.π F βN := by group
          _ = ybar * ybar * NBar.π F βN := by rw [h]
      have hu'' : NBar.ρ F (NBar.π F βN) u = u' := by
        show NBar.ρ F (NBar.π F βN) (NBar.ρ F ybar w) = NBar.ρ F ybar (NBar.ρ F ybar w)
        rw [← MulAut.mul_apply, ← map_mul, hβy, map_mul, map_mul, MulAut.mul_apply,
          MulAut.mul_apply, hβw]
      rcases htvc.2 u with h1 | h1
      · exact huu' (h1.symm.trans hu'')
      · have hwc : w = c := by
          have h2 : w * u = u * c := hwu.trans (hu''.symm.trans h1)
          rw [mul_comm u c] at h2
          exact mul_right_cancel h2
        apply D.a_not_mem_B
        have : (c : G) = D.a := (congrArg Subtype.val hwc).symm
        rw [← this]
        exact hcB
  have hfixu : ∀ βN : ↥(normalizer (F : Set G)), NBar.π F βN * ybar = ybar * NBar.π F βN →
      (βN : G) * D.a * (βN : G)⁻¹ = D.a → (βN : G) * u * (βN : G)⁻¹ = u := by
    intro βN hc ha
    have hβw : NBar.ρ F (NBar.π F βN) w = w := Subtype.ext (by rw [NBar.ρ_π]; exact ha)
    have h1 : NBar.ρ F (NBar.π F βN) u = u := by
      show NBar.ρ F (NBar.π F βN) (NBar.ρ F ybar w) = NBar.ρ F ybar w
      rw [← MulAut.mul_apply, ← map_mul, hc, map_mul, MulAut.mul_apply, hβw]
    have h' := congrArg Subtype.val h1
    rwa [NBar.ρ_π] at h'
  have hfixb : ∀ (βN : ↥(normalizer (F : Set G))) (c : ↥F),
      IsTransvectionWith (NBar.ρ F (NBar.π F βN)) c → NBar.ρ F (NBar.π F βN) ≠ 1 →
      NBar.π F βN * ybar = ybar * NBar.π F βN → NBar.ρ F ybar c = c := by
    intro βN c htvc hne hc
    have h1 : NBar.ρ F ybar * NBar.ρ F (NBar.π F βN) * (NBar.ρ F ybar)⁻¹ =
        NBar.ρ F (NBar.π F βN) := by
      rw [← map_mul, ← hc, map_mul, mul_inv_cancel_right]
    have h2 := B1.tv_conj htvc (NBar.ρ F ybar)
    rw [h1] at h2
    exact NBar.eq_of_isTransvectionWith h2 htvc hne
  obtain ⟨d₀, hd₀R, -, hd₀F, hd₀N, hd₀c⟩ := D.exists_d₀ hF
  have hd₀B₀ : d₀ ∈ D.B₀ := (mem_inf.1 hd₀R).1
  have hd₀T : d₀ ∈ (T : Subgroup G) := D.B_le_T (D.B₀_le_B hd₀B₀)
  have htv₀ : IsTransvectionWith (NBar.ρ F (NBar.π F ⟨d₀, hd₀N⟩)) ⟨D.b₀, hb₀F⟩ :=
    NBar.isTransvectionWith_of_commutator F ⟨d₀, hd₀N⟩ hb₀F D.b₀_ne_one D.b₀_mul_b₀ hd₀c.le
  have hc₀ := hcent ⟨d₀, hd₀N⟩ (D.B₀_le_B hd₀B₀) ⟨D.b₀, hb₀F⟩ D.b₀_mem_B htv₀
  obtain ⟨d₁, hd₁R, -, hd₁F, hd₁N, hd₁c⟩ := D.exists_d₁ hF
  have hd₁B₁ : d₁ ∈ D.B₁ := (mem_inf.1 hd₁R).1
  have hd₁T : d₁ ∈ (T : Subgroup G) := D.B_le_T (D.B₁_le_B hd₁B₁)
  have htv₁ : IsTransvectionWith (NBar.ρ F (NBar.π F ⟨d₁, hd₁N⟩)) ⟨D.b₁, hb₁F⟩ :=
    NBar.isTransvectionWith_of_commutator F ⟨d₁, hd₁N⟩ hb₁F D.b₁_ne_one D.b₁_mul_b₁ hd₁c.le
  have hc₁ := hcent ⟨d₁, hd₁N⟩ (D.B₁_le_B hd₁B₁) ⟨D.b₁, hb₁F⟩ D.b₁_mem_B htv₁
  obtain ⟨α, hαFA, r₀, hr₀, r₁, hr₁, hu_eq⟩ := (D.mem_E64_iff hF).1 u.2
  have hαA : α ∈ D.A := (mem_inf.1 hαFA).2
  have hr₀B₀ : r₀ ∈ D.B₀ := (mem_inf.1 hr₀).2
  have hr₁B₁ : r₁ ∈ D.B₁ := (mem_inf.1 hr₁).2
  have hdecomp₀ : ∀ β ∈ D.B₀, ∀ α' ∈ D.A, ∀ r₀' r₁' : G, r₁' ∈ D.B₁ →
      β * (α' * (r₀' * r₁')) * β⁻¹ = α' * ((β * r₀' * β⁻¹) * r₁') := by
    intro β hβ α' hα' r₀' r₁' hr₁'
    have e1 : α' * β = β * α' := D.A_comm_B α' hα' β (D.B₀_le_B hβ)
    have e2 : β * r₁' = r₁' * β := D.B₀_comm_B₁ β hβ r₁' hr₁'
    calc β * (α' * (r₀' * r₁')) * β⁻¹ = (β * α') * r₀' * r₁' * β⁻¹ := by group
      _ = α' * β * r₀' * r₁' * β⁻¹ := by rw [e1]
      _ = α' * (β * r₀' * β⁻¹) * (β * r₁') * β⁻¹ := by group
      _ = α' * (β * r₀' * β⁻¹) * (r₁' * β) * β⁻¹ := by rw [e2]
      _ = α' * ((β * r₀' * β⁻¹) * r₁') := by group
  have hdecomp₁ : ∀ β ∈ D.B₁, ∀ α' ∈ D.A, ∀ r₀' r₁' : G, r₀' ∈ D.B₀ →
      β * (α' * (r₀' * r₁')) * β⁻¹ = α' * (r₀' * (β * r₁' * β⁻¹)) := by
    intro β hβ α' hα' r₀' r₁' hr₀'
    have e1 : α' * β = β * α' := D.A_comm_B α' hα' β (D.B₁_le_B hβ)
    have e2 : r₀' * β = β * r₀' := D.B₀_comm_B₁ r₀' hr₀' β hβ
    calc β * (α' * (r₀' * r₁')) * β⁻¹ = (β * α') * r₀' * r₁' * β⁻¹ := by group
      _ = α' * β * r₀' * r₁' * β⁻¹ := by rw [e1]
      _ = α' * (β * r₀') * r₁' * β⁻¹ := by group
      _ = α' * (r₀' * β) * r₁' * β⁻¹ := by rw [e2]
      _ = α' * (r₀' * (β * r₁' * β⁻¹)) := by group
  have hd₀a : d₀ * D.a * d₀⁻¹ = D.a := by
    rw [← D.A_comm_B D.a D.a_mem d₀ (D.B₀_le_B hd₀B₀), mul_inv_cancel_right]
  have hd₁a : d₁ * D.a * d₁⁻¹ = D.a := by
    rw [← D.A_comm_B D.a D.a_mem d₁ (D.B₁_le_B hd₁B₁), mul_inv_cancel_right]
  have hr₀' : r₀ = 1 ∨ r₀ = D.b₀ := by
    have hfix := hfixu ⟨d₀, hd₀N⟩ hc₀ hd₀a
    rw [hu_eq, hdecomp₀ d₀ hd₀B₀ α hαA r₀ r₁ hr₁B₁] at hfix
    have hfix' : d₀ * r₀ * d₀⁻¹ = r₀ := mul_right_cancel (mul_left_cancel hfix)
    have hfour := (D.E64_decomp hF).2.2.1
    refine eq_one_or_eq_of_fix_four hfour.2.1 hfour.2.2 (mem_inf.2 ⟨hb₀F, D.b₀_mem⟩)
      D.b₀_ne_one (by rw [D.b₀_comm d₀ hd₀B₀, mul_inv_cancel_right]) ?_ hr₀ hfix'
    obtain ⟨v, hv⟩ := B1.exists_moved_of_ne_one (hρne ⟨d₀, hd₀N⟩ hd₀T hd₀F)
    obtain ⟨α', hα', v₀, hv₀, v₁, hv₁, hveq⟩ := (D.mem_E64_iff hF).1 v.2
    refine ⟨v₀, hv₀, fun h => hv (Subtype.ext ?_)⟩
    rw [NBar.ρ_π]
    show d₀ * (v : G) * d₀⁻¹ = v
    rw [hveq, hdecomp₀ d₀ hd₀B₀ α' (mem_inf.1 hα').2 v₀ v₁ (mem_inf.1 hv₁).2, h]
  have hr₁' : r₁ = 1 ∨ r₁ = D.b₁ := by
    have hfix := hfixu ⟨d₁, hd₁N⟩ hc₁ hd₁a
    rw [hu_eq, hdecomp₁ d₁ hd₁B₁ α hαA r₀ r₁ hr₀B₀] at hfix
    have hfix' : d₁ * r₁ * d₁⁻¹ = r₁ := mul_left_cancel (mul_left_cancel hfix)
    have hfour := (D.E64_decomp hF).2.2.2
    refine eq_one_or_eq_of_fix_four hfour.2.1 hfour.2.2 (mem_inf.2 ⟨hb₁F, D.b₁_mem⟩)
      D.b₁_ne_one (by rw [D.b₁_comm d₁ hd₁B₁, mul_inv_cancel_right]) ?_ hr₁ hfix'
    obtain ⟨v, hv⟩ := B1.exists_moved_of_ne_one (hρne ⟨d₁, hd₁N⟩ hd₁T hd₁F)
    obtain ⟨α', hα', v₀, hv₀, v₁, hv₁, hveq⟩ := (D.mem_E64_iff hF).1 v.2
    refine ⟨v₁, hv₁, fun h => hv (Subtype.ext ?_)⟩
    rw [NBar.ρ_π]
    show d₁ * (v : G) * d₁⁻¹ = v
    rw [hveq, hdecomp₁ d₁ hd₁B₁ α' (mem_inf.1 hα').2 v₀ v₁ (mem_inf.1 hv₀).2, h]
  obtain ⟨yN, hyN⟩ := NBar.π_surjective F ybar
  have huval : (u : G) = yN * D.a * (yN : G)⁻¹ := by
    show ((NBar.ρ F ybar w : ↥F) : G) = _
    rw [← hyN, NBar.ρ_π]
  have hconj_u : IsConj D.a (u : G) := isConj_iff.2 ⟨yN, huval.symm⟩
  have haZ : D.a ∈ D.Zab := subset_closure (Set.mem_insert _ _)
  have hb₀Z : D.b₀ ∈ D.Zab := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb₁Z : D.b₁ ∈ D.Zab :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hr₀Z : r₀ ∈ D.Zab := by
    rcases hr₀' with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hb₀Z
  have hr₁Z : r₁ ∈ D.Zab := by
    rcases hr₁' with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hb₁Z
  have hα1 : α ≠ 1 := by
    intro h
    have hu' : (u : G) ∈ D.Zab := by
      rw [hu_eq, h, one_mul]
      exact mul_mem hr₀Z hr₁Z
    apply huA
    rw [hL3 _ hu' hconj_u]
    exact D.a_mem
  have hαa : α ≠ D.a := by
    intro h
    have hu' : (u : G) ∈ D.Zab := by
      rw [hu_eq, h]
      exact mul_mem haZ (mul_mem hr₀Z hr₁Z)
    apply huA
    rw [hL3 _ hu' hconj_u]
    exact D.a_mem
  have huinv : (u : G) * u = 1 := hF2 _ u.2
  have huJoin : (u : G) ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
    rw [hu_eq]
    refine mul_mem (mem_sup_left hαA) (mem_sup_right (mul_mem (mem_sup_left ?_) (mem_sup_right ?_)))
    · rcases hr₀' with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers _
    · rcases hr₁' with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers _
  obtain ⟨E', hE', hPE', huE'⟩ := hP _ huJoin huinv
  refine ⟨⟨yN, E', hE', hPE', by rw [← huval]; exact huE', by rw [← huval]; exact huA⟩,
    fun hPF => ?_⟩
  obtain ⟨s', hs'BN, hs'map⟩ := hS F hF hPF
  have hs'B : s' ∈ D.B := (mem_inf.1 hs'BN).1
  have hs'N : s' ∈ normalizer (F : Set G) := (mem_inf.1 hs'BN).2
  have hs'T : s' ∈ (T : Subgroup G) := D.B_le_T hs'B
  have hs'b₀ : s' * D.b₀ * s'⁻¹ = D.b₁ := by
    have hmem : s' * D.b₀ * s'⁻¹ ∈ D.B₁ := by
      rw [← hs'map]
      exact ⟨D.b₀, D.b₀_mem, by simp [MulAut.conj_apply]⟩
    have hcomm : ∀ y ∈ D.B₁, y * (s' * D.b₀ * s'⁻¹) = (s' * D.b₀ * s'⁻¹) * y := by
      intro y hy
      rw [← hs'map] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hc := D.b₀_comm y₀ hy₀
      calc s' * y₀ * s'⁻¹ * (s' * D.b₀ * s'⁻¹) = s' * (y₀ * D.b₀) * s'⁻¹ := by group
        _ = s' * (D.b₀ * y₀) * s'⁻¹ := by rw [hc]
        _ = s' * D.b₀ * s'⁻¹ * (s' * y₀ * s'⁻¹) := by group
    rcases D.eq_one_or_b₁_of_comm hmem hcomm with h | h
    · exact absurd (conj_eq_one_iff.1 h) D.b₀_ne_one
    · exact h
  have hs₀ : ∃ s₀ : ↥(normalizer (F : Set G)), (s₀ : G) ∈ (T : Subgroup G) ∧
      (∃ δ ∈ D.A, (s₀ : G) = s' * δ) ∧ NBar.π F s₀ * ybar = ybar * NBar.π F s₀ := by
    rcases hconj_cases (NBar.π F ⟨s', hs'N⟩) with h | h
    · refine ⟨⟨s', hs'N⟩, hs'T, ⟨1, one_mem _, (mul_one _).symm⟩, ?_⟩
      calc NBar.π F ⟨s', hs'N⟩ * ybar
          = NBar.π F ⟨s', hs'N⟩ * ybar * (NBar.π F ⟨s', hs'N⟩)⁻¹ * NBar.π F ⟨s', hs'N⟩ := by
            group
        _ = ybar * NBar.π F ⟨s', hs'N⟩ := by rw [h]
    · refine ⟨⟨s', hs'N⟩ * dN, mul_mem hs'T hdT, ⟨d, hdA, rfl⟩, ?_⟩
      have hdy : dbar * ybar * dbar⁻¹ = ybar⁻¹ := hyb.conj_eq_inv
      have hyy : (ybar * ybar)⁻¹ = ybar :=
        inv_eq_of_mul_eq_one_left (by rw [← pow_three]; exact h3)
      have key : NBar.π F ⟨s', hs'N⟩ * dbar * ybar * (NBar.π F ⟨s', hs'N⟩ * dbar)⁻¹ = ybar := by
        calc NBar.π F ⟨s', hs'N⟩ * dbar * ybar * (NBar.π F ⟨s', hs'N⟩ * dbar)⁻¹
            = NBar.π F ⟨s', hs'N⟩ * (dbar * ybar * dbar⁻¹) * (NBar.π F ⟨s', hs'N⟩)⁻¹ := by
              group
          _ = (NBar.π F ⟨s', hs'N⟩ * ybar * (NBar.π F ⟨s', hs'N⟩)⁻¹)⁻¹ := by rw [hdy]; group
          _ = ybar := by rw [h, hyy]
      rw [map_mul]
      calc NBar.π F ⟨s', hs'N⟩ * dbar * ybar
          = NBar.π F ⟨s', hs'N⟩ * dbar * ybar * (NBar.π F ⟨s', hs'N⟩ * dbar)⁻¹ *
              (NBar.π F ⟨s', hs'N⟩ * dbar) := by group
        _ = ybar * (NBar.π F ⟨s', hs'N⟩ * dbar) := by rw [key]
  obtain ⟨s₀, hs₀T, ⟨δ, hδA, hs₀eq⟩, hs₀c⟩ := hs₀
  have hs₀a : (s₀ : G) * D.a * (s₀ : G)⁻¹ = D.a := by
    rw [D.a_comm_T hs₀T, mul_inv_cancel_right]
  have hs₀u := hfixu s₀ hs₀c hs₀a
  have hδb : ∀ β ∈ D.B, δ * β * δ⁻¹ = β := fun β hβ => by
    rw [D.A_comm_B δ hδA β hβ, mul_inv_cancel_right]
  have hs₀b₀ : (s₀ : G) * D.b₀ * (s₀ : G)⁻¹ = D.b₁ := by
    rw [hs₀eq]
    calc s' * δ * D.b₀ * (s' * δ)⁻¹ = s' * (δ * D.b₀ * δ⁻¹) * s'⁻¹ := by group
      _ = D.b₁ := by rw [hδb _ D.b₀_mem_B, hs'b₀]
  have hs₀b₁B : (s₀ : G) * D.b₁ * (s₀ : G)⁻¹ ∈ D.B :=
    (mem_normalizer_iff.1 (D.T_le_normalizer_B hs₀T) D.b₁).1 D.b₁_mem_B
  have hs₀b₁ : (s₀ : G) * D.b₁ * (s₀ : G)⁻¹ ≠ D.b₁ := by
    intro h
    apply D.b₀_ne_b₁
    exact mul_left_cancel (mul_right_cancel (hs₀b₀.trans h.symm))
  have hs₀α : (s₀ : G) * α * (s₀ : G)⁻¹ ∈ D.A :=
    (mem_normalizer_iff.1 (D.T_le_normalizer_A hs₀T) α).1 hαA
  have hfactor : ∀ {α₁ α₂ β₁ β₂ : G}, α₁ ∈ D.A → α₂ ∈ D.A → β₁ ∈ D.B → β₂ ∈ D.B →
      α₁ * β₁ = α₂ * β₂ → β₁ = β₂ := fun h1 h2 h3 h4 h =>
    (TStruct.eq_and_eq_of_mul_eq_mul D.A_inf_B h1 h2 h3 h4 h).2
  have hsplit : ∀ z : G, (s₀ : G) * (α * z) * (s₀ : G)⁻¹ =
      ((s₀ : G) * α * (s₀ : G)⁻¹) * ((s₀ : G) * z * (s₀ : G)⁻¹) := fun z => by group
  have hr : r₀ = D.b₀ ∧ r₁ = D.b₁ := by
    rcases hr₀' with h0 | h0 <;> rcases hr₁' with h1 | h1
    · exfalso
      apply huA
      rw [hu_eq, h0, h1, one_mul, mul_one]
      exact hαA
    · exfalso
      rw [hu_eq, h0, h1, one_mul, hsplit] at hs₀u
      exact hs₀b₁ (hfactor hs₀α hαA hs₀b₁B D.b₁_mem_B hs₀u)
    · exfalso
      rw [hu_eq, h0, h1, mul_one, hsplit, hs₀b₀] at hs₀u
      exact D.b₀_ne_b₁ (hfactor hs₀α hαA D.b₁_mem_B D.b₀_mem_B hs₀u).symm
    · exact ⟨h0, h1⟩
  obtain ⟨hr₀b, hr₁b⟩ := hr
  have hyb₀ : (yN : G) * D.b₀ * (yN : G)⁻¹ = D.b₀ := by
    have h1 := hfixb ⟨d₀, hd₀N⟩ ⟨D.b₀, hb₀F⟩ htv₀ (hρne _ hd₀T hd₀F) hc₀
    have h' := congrArg Subtype.val h1
    rw [← hyN, NBar.ρ_π] at h'
    exact h'
  have hyb₁ : (yN : G) * D.b₁ * (yN : G)⁻¹ = D.b₁ := by
    have h1 := hfixb ⟨d₁, hd₁N⟩ ⟨D.b₁, hb₁F⟩ htv₁ (hρne _ hd₁T hd₁F) hc₁
    have h' := congrArg Subtype.val h1
    rw [← hyN, NBar.ρ_π] at h'
    exact h'
  refine ⟨yN, α, hαA, orderOf_eq_prime (by rw [sq]; exact hF2 α (mem_inf.1 hαFA).1) hα1, hαa,
    ?_, ?_⟩
  · rw [← huval, hu_eq, hr₀b, hr₁b]
    rfl
  · show (yN : G) * (D.b₀ * D.b₁) * (yN : G)⁻¹ = D.b₀ * D.b₁
    calc (yN : G) * (D.b₀ * D.b₁) * (yN : G)⁻¹
        = ((yN : G) * D.b₀ * (yN : G)⁻¹) * ((yN : G) * D.b₁ * (yN : G)⁻¹) := by group
      _ = D.b₀ * D.b₁ := by rw [hyb₀, hyb₁]

theorem lemma6Key_of (P : Subgroup G → Prop)
    (hL3 : ∀ y ∈ D.Zab, IsConj D.a y → y = D.a)
    (hL4 : ∀ g : G, g * D.a * g⁻¹ ∈ (T : Subgroup G) → g * D.a * g⁻¹ ∈ D.T₁)
    (hL5 : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∀ g : G,
      E.map (MulAut.conj g).toMonoidHom ≤ T →
      ∃ h ∈ (T : Subgroup G), E.map (MulAut.conj g).toMonoidHom = E.map (MulAut.conj h).toMonoidHom)
    (hSylN : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∃ Q : Sylow 2 ↥(normalizer (E : Set G)),
      (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (E : Set G)))
    (hTv : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∀ x c : G, x ∈ (T : Subgroup G) →
      x ∈ normalizer (E : Set G) → (∀ v ∈ E, x * v * x⁻¹ = v ∨ x * v * x⁻¹ = v * c) →
      (∃ v ∈ E, x * v * x⁻¹ ≠ v) →
      (∃ α ∈ D.A, x * α⁻¹ ∈ E) ∨ (∃ β ∈ D.B₀, x * β⁻¹ ∈ E) ∨ (∃ β ∈ D.B₁, x * β⁻¹ ∈ E))
    (hS : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → P E →
      ∃ s' ∈ D.B ⊓ normalizer (E : Set G), D.B₀.map (MulAut.conj s').toMonoidHom = D.B₁)
    (hP : ∀ x ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), x * x = 1 →
      ∃ E : Subgroup G, IsE64 (T : Subgroup G) E ∧ P E ∧ x ∈ E)
    (hx : ∃ x : G, x * D.a * x⁻¹ ∈ (T : Subgroup G) ∧ x * D.a * x⁻¹ ∉ D.A) :
    ∃ y : G, ∃ a₁ ∈ D.A, orderOf a₁ = 2 ∧ a₁ ≠ D.a ∧ y * D.a * y⁻¹ = a₁ * D.b ∧
      y * D.b * y⁻¹ = D.b := by
  have hTC : (T : Subgroup G) ≤ centralizer ({D.a} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.2 (D.a_comm_T hy)
  have hnorm : ∀ {x : G} {F : Subgroup G}, IsE64 (T : Subgroup G) F → x * D.a * x⁻¹ ∈ F →
      x * D.a * x⁻¹ ∉ D.A → ∃ x' ∈ normalizer (F : Set G), x' * D.a * x'⁻¹ ∈ F ∧
        x' * D.a * x'⁻¹ ∉ D.A := by
    intro x F hF hxF hxA
    have hF2 : IsPGroup 2 F := IsPGroup.of_card hF.2.2
    obtain ⟨n', hn'N, h, hhT, -, hn'eq⟩ := exists_normalizer_conj (T.subtype hTC)
      (Sylow.coe_subtype T hTC) le_rfl hF2
      (fun u hu v hv => TStruct.comm_of_mul_self hF.mul_self hu hv) hxF (hL5 F hF)
    have hha : h⁻¹ * D.a * h = D.a := by
      rw [mul_assoc, ← D.a_comm_T hhT, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hha] at hn'eq
    exact ⟨n', hn'N, by rw [hn'eq]; exact hxF, by rw [hn'eq]; exact hxA⟩
  obtain ⟨x, hxT, hxA⟩ := hx
  have hx2 : x * D.a * x⁻¹ * (x * D.a * x⁻¹) = 1 := by
    calc x * D.a * x⁻¹ * (x * D.a * x⁻¹) = x * (D.a * D.a) * x⁻¹ := by group
      _ = 1 := by rw [D.a_mul_a, mul_one, mul_inv_cancel]
  obtain ⟨F, hFT₁, hFab, hFcard, hxF⟩ := D.exists_elem64_of_mem_T₁ (hL4 x hxT) hx2
  have hF : IsE64 (T : Subgroup G) F := ⟨hFT₁.trans D.T₁_le_T, hFab, hFcard⟩
  obtain ⟨x', hx'N, hx'F, hx'A⟩ := hnorm hF hxF hxA
  obtain ⟨⟨x'', F', hF', hPF', hx''F, hx''A⟩, -⟩ :=
    D.lemma6Key_core P hL3 hSylN hTv hS hP hF hx'N hx'F hx'A
  obtain ⟨x₃, hx₃N, hx₃F, hx₃A⟩ := hnorm hF' hx''F hx''A
  exact (D.lemma6Key_core P hL3 hSylN hTv hS hP hF' hx₃N hx₃F hx₃A).2 hPF'

end FooteCore

end CFSG.CGT.Foote81L6
