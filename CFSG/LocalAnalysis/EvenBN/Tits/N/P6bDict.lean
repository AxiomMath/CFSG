module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bJ

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section Gen

variable {G : Type*} [Group G] (S : Subgroup G)

theorem isElemAbQuot_map (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hs : ∀ a ∈ S, a * a = 1)
    {Z₁ V₁ : Subgroup S} (hZV : Z₁ ≤ V₁) {n : ℕ} (hn : Z₁.relIndex V₁ = 2 ^ n) :
    IsElemAbQuot (V₁.map S.subtype) (Z₁.map S.subtype) n := by
  have hmemS : ∀ k : G, k ∈ V₁.map S.subtype → k ∈ S := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  refine ⟨Subgroup.map_mono hZV, ⟨fun n hn g => ?_⟩, fun k hk => ?_, fun a ha b hb => ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnS := hmemS _ n.2
    have hgS := hmemS _ g.2
    have e : (g : G) * n * (g : G)⁻¹ = n := by
      rw [hc _ hgS _ hnS]; group
    show ((g * n * g⁻¹ : ↥(V₁.map S.subtype)) : G) ∈ Z₁.map S.subtype
    rw [show ((g * n * g⁻¹ : ↥(V₁.map S.subtype)) : G) = (g : G) * n * (g : G)⁻¹ from rfl, e]
    exact hn
  · rw [hs k (hmemS k hk)]
    exact one_mem _
  · have hc' : a * b * a⁻¹ * b⁻¹ = 1 := by
      rw [hc a (hmemS a ha) b (hmemS b hb)]; group
    rw [hc']
    exact one_mem _
  · rw [Subgroup.relIndex_map_map_of_injective Z₁ V₁ S.subtype_injective]
    exact hn

end Gen

section Shapes

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

@[expose] def N23bA6 (d : Data G) (z₀ : G) : Prop :=
  (∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
      Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* alternatingGroup (Fin 6))) ∧
    ∃ V₁ V₂ : Subgroup G, Zz d z₀ ≤ V₁ ∧ V₁ ≤ d.s56V ∧ Zz d z₀ ≤ V₂ ∧ V₂ ≤ d.s56V ∧
      V₁ ⊔ V₂ = d.s56V ∧ V₁ ⊓ V₂ = Zz d z₀ ∧
      (∀ j ∈ Jp d, ∀ v ∈ V₁, j * v * j⁻¹ ∈ V₁) ∧ (∀ j ∈ Jp d, ∀ v ∈ V₂, j * v * j⁻¹ ∈ V₂) ∧
      V₂ = V₁.map (MulAut.conj d.t).toMonoidHom ∧
      IsElemAbQuot V₁ (Zz d z₀) 4 ∧ IsElemAbQuot V₂ (Zz d z₀) 4 ∧
      (∀ U : Subgroup G, Zz d z₀ ≤ U → U ≤ V₁ → (∀ j ∈ Jp d, ∀ u ∈ U, j * u * j⁻¹ ∈ U) →
        U = Zz d z₀ ∨ U = V₁) ∧
      (∀ U : Subgroup G, Zz d z₀ ≤ U → U ≤ V₂ → (∀ j ∈ Jp d, ∀ u ∈ U, j * u * j⁻¹ ∈ U) →
        U = Zz d z₀ ∨ U = V₂) ∧
      centralizerMod (Jp d) (Zz d z₀) V₁ = Wg d z₀ ∧ centralizerMod (Jp d) (Zz d z₀) V₂ = Wg d z₀

@[expose] def N23bE25 (d : Data G) (z₀ : G) : Prop :=
  (∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
      Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃*
        Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) ∧
    ∃ J₁ J₂ V₁ V₂ : Subgroup G, Wg d z₀ ≤ J₁ ∧ J₁ ≤ Jp d ∧ Wg d z₀ ≤ J₂ ∧ J₂ ≤ Jp d ∧
      J₁ ⊔ J₂ = Jp d ∧ J₁ ⊓ J₂ = Wg d z₀ ∧
      (Wg d z₀).relIndex J₁ = 5 ∧ (Wg d z₀).relIndex J₂ = 5 ∧
      V₁ = centralizerMod d.s56V (Zz d z₀) J₁ ∧ V₂ = centralizerMod d.s56V (Zz d z₀) J₂ ∧
      V₁ ⊔ V₂ = d.s56V ∧ V₁ ⊓ V₂ = Zz d z₀ ∧
      IsElemAbQuot V₁ (Zz d z₀) 4 ∧ IsElemAbQuot V₂ (Zz d z₀) 4 ∧
      V₂ = V₁.map (MulAut.conj d.t).toMonoidHom

theorem node23b_iff : Node23b d z₀ ↔ (⁅d.s56V, Wg d z₀⁆ = Zz d z₀ ∧ (N23bA6 d z₀ ∨ N23bE25 d z₀)) :=
  Iff.rfl

end Shapes


section GenPre

variable {Γ : Type*} [Group Γ]

theorem relIndex_preIn {S : Subgroup Γ} {K₁ K₂ : Subgroup (MulAut ↥S)}
    (h₂ : K₂ ≤ imgIn S (normalizer (S : Set Γ))) :
    (preIn S K₁).relIndex (preIn S K₂) = K₁.relIndex K₂ := by
  unfold preIn
  rw [Subgroup.relIndex_map_map_of_injective _ _ (Subgroup.subtype_injective _),
    Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_eq_right.2]
  rwa [← imgIn_normalizer S]

end GenPre

section DictD

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem mem_Jb_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (σ : ↥(Hs d)) :
    σ ∈ normalClosure ({xB h49 hd} : Set ↥(Hs d)) ↔ (σ : MulAut ↥d.s56V) ∈ img d (Jg d) := by
  rw [← Jb_map_eq h49 hd]
  constructor
  · intro h
    exact Subgroup.mem_map_of_mem _ h
  · rintro ⟨σ', hσ', h⟩
    have : σ' = σ := Subtype.ext h
    rwa [← this]

theorem starB_mem_Jb (h49 : d.Thm49Statement) (hd : d.Hyp) {j : G} (hj : j ∈ Jp d) :
    starB d j ((mem_preIn_iff d.s56V _).1 hj).1 ∈ normalClosure ({xB h49 hd} : Set ↥(Hs d)) :=
  (mem_Jb_iff h49 hd _).2 ((mem_preIn_iff d.s56V _).1 hj).2

theorem exists_lift_Jb (h49 : d.Thm49Statement) (hd : d.Hyp) {σ : ↥(Hs d)}
    (hσ : σ ∈ normalClosure ({xB h49 hd} : Set ↥(Hs d))) :
    ∃ j ∈ Jp d, ∃ hj : j ∈ Hg d, starB d j hj = σ := by
  obtain ⟨g, hg, hgσ⟩ := (mem_Js_iff).1 ((mem_Jb_iff h49 hd σ).1 hσ)
  have hgH : g ∈ Hg d := Jg_le_Hg d hg
  refine ⟨g, (mem_preIn_iff d.s56V _).2 ⟨hgH, ?_⟩, hgH, Subtype.ext hgσ⟩
  rw [show actFun d.s56V g = star d g from rfl, hgσ]
  exact (mem_Jb_iff h49 hd σ).1 hσ

theorem Zv_map (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    (Zv d z₀).map d.s56V.subtype = Zz d z₀ :=
  Subgroup.map_subgroupOf_eq_of_le (Z_le_V h49 hd hz)

theorem mem_normalizer_Z (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀) {g : G}
    (hg : g ∈ Hg d) : g ∈ normalizer (Zz d z₀ : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hZH g hg y hy, fun hy => ?_⟩
  have := hZH g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem inv_transfer (h49 : d.Thm49Statement) (hd : d.Hyp) {V₁ : Subgroup ↥d.s56V}
    (h : ∀ σ ∈ normalClosure ({xB h49 hd} : Set ↥(Hs d)), ∀ v ∈ V₁, (σ : MulAut ↥d.s56V) v ∈ V₁) :
    ∀ j ∈ Jp d, ∀ v ∈ V₁.map d.s56V.subtype, j * v * j⁻¹ ∈ V₁.map d.s56V.subtype := by
  rintro j hj _ ⟨u, hu, rfl⟩
  have hjH : j ∈ Hg d := ((mem_preIn_iff d.s56V _).1 hj).1
  have h1 := h _ (starB_mem_Jb h49 hd hj) u hu
  exact ⟨_, h1, star_apply_val hjH u⟩

theorem conj_transfer {g : G} (hg : g ∈ Hg d) (V₁ : Subgroup ↥d.s56V) :
    (V₁.map ((starB d g hg : MulAut ↥d.s56V) : ↥d.s56V →* ↥d.s56V)).map d.s56V.subtype =
      (V₁.map d.s56V.subtype).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext u
  exact star_apply_val hg u

theorem irr_transfer (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    {V₁ : Subgroup ↥d.s56V} (hZV₁ : Zv d z₀ ≤ V₁)
    (hirr : ∀ U : Subgroup ↥d.s56V, Zv d z₀ ≤ U → U ≤ V₁ →
      (∀ σ ∈ normalClosure ({xB h49 hd} : Set ↥(Hs d)), ∀ u ∈ U, (σ : MulAut ↥d.s56V) u ∈ U) →
        U = Zv d z₀ ∨ U = V₁) :
    ∀ U : Subgroup G, Zz d z₀ ≤ U → U ≤ V₁.map d.s56V.subtype →
      (∀ j ∈ Jp d, ∀ u ∈ U, j * u * j⁻¹ ∈ U) → U = Zz d z₀ ∨ U = V₁.map d.s56V.subtype := by
  intro U hZU hUV hUinv
  have hUV' : U ≤ d.s56V := hUV.trans (Subgroup.map_subtype_le _)
  have hmapU : (U.subgroupOf d.s56V).map d.s56V.subtype = U :=
    Subgroup.map_subgroupOf_eq_of_le hUV'
  have h1 : Zv d z₀ ≤ U.subgroupOf d.s56V := fun y hy =>
    Subgroup.mem_subgroupOf.2 (hZU ((Subgroup.mem_subgroupOf).1 hy))
  have h2 : U.subgroupOf d.s56V ≤ V₁ := by
    intro y hy
    obtain ⟨u, hu, hu'⟩ := hUV (Subgroup.mem_subgroupOf.1 hy)
    have : u = y := Subtype.ext hu'
    rwa [← this]
  have h3 : ∀ σ ∈ normalClosure ({xB h49 hd} : Set ↥(Hs d)), ∀ u ∈ U.subgroupOf d.s56V,
      (σ : MulAut ↥d.s56V) u ∈ U.subgroupOf d.s56V := by
    intro σ hσ u hu
    obtain ⟨j, hj, hjH, rfl⟩ := exists_lift_Jb h49 hd hσ
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    have := hUinv j hj u hu
    rwa [show ((starB d j hjH : MulAut ↥d.s56V) u : G) = j * (u : G) * j⁻¹ from star_apply_val hjH u]
  rcases hirr _ h1 h2 h3 with h | h
  · left
    rw [← hmapU, h, Zv_map h49 hd hz]
  · right
    rw [← hmapU, h]

theorem cent_transfer (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hc : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a)
    (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    (hWimg : img d (Wg d z₀) = Ws d) (hWJ : Ws d ≤ img d (Jg d))
    (hcomm : ∀ w ∈ Wg d z₀, ∀ v ∈ d.s56V, w * v * w⁻¹ * v⁻¹ ∈ Zz d z₀)
    {V₁ : Subgroup ↥d.s56V}
    (hfaith : ∀ σ ∈ normalClosure ({xB h49 hd} : Set ↥(Hs d)),
      (∀ v ∈ V₁, v⁻¹ * (σ : MulAut ↥d.s56V) v ∈ Zv d z₀) → (σ : MulAut ↥d.s56V) ∈ Ws d) :
    centralizerMod (Jp d) (Zz d z₀) (V₁.map d.s56V.subtype) = Wg d z₀ := by
  ext g
  constructor
  · rintro ⟨hgJp, hgN, hg⟩
    have hgH : g ∈ Hg d := ((mem_preIn_iff d.s56V _).1 hgJp).1
    have hσ := starB_mem_Jb h49 hd hgJp
    have key := hfaith _ hσ (fun v hv => by
      show ((v⁻¹ * star d g v : ↥d.s56V) : G) ∈ Zz d z₀
      have h1 : ((v⁻¹ * star d g v : ↥d.s56V) : G) = (v : G)⁻¹ * (g * v * g⁻¹) := by
        show (v : G)⁻¹ * ((star d g v : ↥d.s56V) : G) = _
        rw [star_apply_val hgH]
      have h2 := hg (v : G) ⟨v, hv, rfl⟩
      have h3 : g * (v : G) * g⁻¹ ∈ d.s56V := by
        have := (star d g v).2
        rwa [star_apply_val hgH] at this
      have h4 : (v : G)⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (v : G)⁻¹ :=
        hc _ (inv_mem v.2) _ h3
      rw [h1, h4]
      exact h2)
    rw [Wg_eq_pre hz hWimg]
    exact (mem_preIn_iff d.s56V _).2 ⟨hgH, key⟩
  · intro hgW
    have hgP := hgW
    rw [Wg_eq_pre hz hWimg] at hgP
    obtain ⟨hgH, hgs⟩ := (mem_preIn_iff d.s56V _).1 hgP
    refine ⟨(mem_preIn_iff d.s56V _).2 ⟨hgH, hWJ hgs⟩, mem_normalizer_Z hZH hgH, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hcomm g hgW u u.2

end DictD






end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
