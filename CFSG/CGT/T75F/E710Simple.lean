module

public import CFSG.CGT.T75F.E710QuotCores
public import CFSG.CGT.T75F.E710Layer
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
public import CFSG.LargeExtraspecial.S111SHCor3
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.T75F

open CFSG.Open CFSG.Goldschmidt CFSG.CGT.Timmesfeld75 CFSG.LargeExtraspecial

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem exists_commuting_pair_hat :
    ∃ x ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D,
      ∃ y ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D, x ≠ y ∧ x * y = y * x := by
  have hq := h.q_ge
  have hnt : 1 < Nat.card L := by rw [h.L_card]; nlinarith
  have : Nontrivial L := Finite.one_lt_card_iff_nontrivial.1 hnt
  obtain ⟨⟨l₁, hl₁⟩, hne⟩ := exists_ne (1 : L)
  have hl₁1 : l₁ ≠ 1 := fun h' => hne (Subtype.ext h')
  have hnotle : ¬ L ≤ Subgroup.zpowers l₁ := by
    intro hle
    have h1 : Nat.card L ≤ Nat.card (Subgroup.zpowers l₁) := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers l₁) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact h.sq_eq_one l₁ (h.L_D l₁ hl₁ hl₁1)) hl₁1
    rw [h2, h.L_card] at h1
    nlinarith
  obtain ⟨l₂, hl₂, hl₂n⟩ := IsConcreteLE.not_le_iff_exists.1 hnotle
  have hl₂1 : l₂ ≠ 1 := fun h' => hl₂n (h' ▸ Subgroup.one_mem _)
  have hl₂l₁ : l₂ ≠ l₁ := fun h' => hl₂n (h' ▸ Subgroup.mem_zpowers l₁)
  refine ⟨QuotientGroup.mk' _ l₁, ⟨l₁, h.L_D l₁ hl₁ hl₁1, rfl⟩, QuotientGroup.mk' _ l₂,
    ⟨l₂, h.L_D l₂ hl₂ hl₂1, rfl⟩, ?_, ?_⟩
  · intro heq
    have hz : l₁⁻¹ * l₂ ∈ Subgroup.center X := by
      rw [← QuotientGroup.eq]
      exact heq
    have hmem : l₁⁻¹ * l₂ ∈ L := L.mul_mem (L.inv_mem hl₁) hl₂
    by_contra _
    have h1 : l₁⁻¹ * l₂ = 1 := by
      by_contra hne1
      exact h.not_mem_center (h.L_D _ hmem hne1) hz
    exact hl₂l₁ (inv_mul_eq_one.1 h1).symm
  · change (QuotientGroup.mk l₁ : X ⧸ Subgroup.center X) * QuotientGroup.mk l₂ =
      QuotientGroup.mk l₂ * QuotientGroup.mk l₁
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h.M_comm l₁ (h.L_le hl₁) l₂ (h.L_le hl₂)]

theorem Dhat_odd {x y : X ⧸ Subgroup.center X}
    (hx : x ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D)
    (hy : y ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D) :
    orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)) := by
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨e, he, rfl⟩ := hy
  have := h.order_mk_mul hd he
  simpa [QuotientGroup.mk_mul] using this

theorem quot_isSimple (hG : Goldschmidt1974) : IsSimpleGroup (X ⧸ Subgroup.center X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hMS⟩ := h.exists_sylow
  obtain ⟨γ, hγD, hγM, hγfix⟩ := h.exists_fixed S hMS
  have hψ : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  let Ŝ : Sylow 2 (X ⧸ Subgroup.center X) := S.mapSurjective hψ
  have hŜ : (Ŝ : Subgroup (X ⧸ Subgroup.center X)) =
      (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)) := Sylow.coe_mapSurjective hψ S
  set γh : X ⧸ Subgroup.center X := QuotientGroup.mk γ with hγh
  have hγhD : γh ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D := ⟨γ, hγD, rfl⟩
  have hγhM : γh ∈ Mhat M := Subgroup.mem_map.2 ⟨γ, hγM, rfl⟩
  have hγhS : γh ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)) := by
    rw [hŜ]
    exact Subgroup.mem_map.2 ⟨γ, hMS hγM, rfl⟩
  have hγhc : ∀ x ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)), x * γh = γh * x := by
    intro x hx
    rw [hŜ] at hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
    change (QuotientGroup.mk s : X ⧸ Subgroup.center X) * QuotientGroup.mk γ =
      QuotientGroup.mk γ * QuotientGroup.mk s
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have := hγfix s hs
    calc s * γ = s * γ * s⁻¹ * s := by group
      _ = γ * s := by rw [this]
  have hle : S11.wcl γh ≤ Mhat M := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨m, hym, hyc⟩
    have hyD : y ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D := by
      rw [hym]
      exact h.Dhat_conj hγhD m
    exact h.H3hat hγhD hγhM hyD hyc
  have hab : IsMulCommutative (S11.wcl γh) :=
    ⟨⟨fun a b => Subtype.ext (h.Mhat_comm (hle a.2) (hle b.2))⟩⟩
  obtain ⟨hWS, hcl⟩ := S11.wcl_stronglyClosed Ŝ hγhS hγhc hab
  obtain ⟨ha, -, -⟩ := hG _ Ŝ (S11.wcl γh) hWS hab hcl
  set A : Subgroup (X ⧸ Subgroup.center X) := S11.wcl γh with hA
  set M' : Subgroup (X ⧸ Subgroup.center X) := Subgroup.normalClosure (A : Set _) with hM'
  have hM'n : M'.Normal := Subgroup.normalClosure_normal
  obtain ⟨x₀, hx₀⟩ := h.Dhat_isConj
  have hM'top : M' = ⊤ := by
    rw [eq_top_iff, ← h.Dhat_closure, Subgroup.closure_le]
    intro x hx
    have h1 : IsConj x₀ x := by
      have : x ∈ {g | IsConj x₀ g} := hx₀ ▸ hx
      exact this
    have h2 : IsConj x₀ γh := by
      have : γh ∈ {g | IsConj x₀ g} := hx₀ ▸ hγhD
      exact this
    obtain ⟨g, hg⟩ := isConj_iff.1 (h2.symm.trans h1)
    rw [← hg]
    exact hM'n.conj_mem γh (Subgroup.subset_normalClosure (S11.self_mem_wcl γh)) g
  let e₁ : (X ⧸ Subgroup.center X) ≃* ↥M' :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hM'top.symm)
  have hO : goldschmidtOddCore ↥M' = ⊥ := by
    refine le_antisymm (sSup_le fun N hN => ?_) bot_le
    obtain ⟨hNn, hNodd⟩ := hN
    have hN' : (N.map e₁.symm.toMonoidHom).Normal := Subgroup.Normal.map hNn _ e₁.symm.surjective
    have hcard : Nat.card (N.map e₁.symm.toMonoidHom) = Nat.card N :=
      Subgroup.card_map_of_injective e₁.symm.injective
    have := h.odd_normal_quot_eq_bot (N.map e₁.symm.toMonoidHom) (by rw [hcard]; exact hNodd)
    intro n hn
    have h1 : e₁.symm n ∈ N.map e₁.symm.toMonoidHom := ⟨n, hn, rfl⟩
    rw [this, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    simpa using h1
  let e₂ : (↥M' ⧸ goldschmidtOddCore ↥M') ≃* ↥M' :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  let eQ : (X ⧸ Subgroup.center X) ≃* (↥M' ⧸ goldschmidtOddCore ↥M') := e₁.trans e₂.symm
  have hmap : (CFSG.Open.pCore 2 (X ⧸ Subgroup.center X) ⊔
      goldschmidtLayer (X ⧸ Subgroup.center X)).map eQ.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, SStarTransport.pCore_map_mulEquiv,
      SStarTransport.goldschmidtLayer_map_mulEquiv']
    exact ha
  have hM : CFSG.Open.pCore 2 (X ⧸ Subgroup.center X) ⊔
      goldschmidtLayer (X ⧸ Subgroup.center X) = ⊤ := by
    apply Subgroup.map_injective (f := eQ.toMonoidHom) eQ.injective
    rw [hmap]
    exact (Subgroup.map_top_of_surjective _ eQ.surjective).symm
  have hP : CFSG.Open.pCore 2 (X ⧸ Subgroup.center X) = ⊥ := by
    exact h.normal_pGroup_quot_eq_bot _ CFSG.pCore_isPGroup
  refine simple_of_layer (E := (QuotientGroup.mk' (Subgroup.center X)) '' D) hM hP
    h.center_quot_eq_bot (fun x hx g => h.Dhat_conj hx g) (fun x hx => h.Dhat_sq hx)
    (fun x hx => h.Dhat_ne_one hx) ?_ h.Dhat_closure ?_ (fun x hx y hy => h.Dhat_odd hx hy)
    h.exists_commuting_pair_hat
  · intro d hd e he
    have h1 : IsConj x₀ d := by
      have : d ∈ {g | IsConj x₀ g} := hx₀ ▸ hd
      exact this
    have h2 : IsConj x₀ e := by
      have : e ∈ {g | IsConj x₀ g} := hx₀ ▸ he
      exact this
    obtain ⟨g, hg⟩ := isConj_iff.1 (h1.symm.trans h2)
    exact ⟨g, hg.symm⟩
  · obtain ⟨y, hy, -⟩ := h.exists_out
    exact ⟨_, ⟨y, hy, rfl⟩⟩

end Endgame710

end CFSG.CGT.T75F
