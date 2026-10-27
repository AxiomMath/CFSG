module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf63E64Aut
public import CFSG.ClassicalInvolution.Q3.TL3T36
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem eq_of_mkQ_mul_eq_zBar {α β : Finset (Fin 7)} {hα : α.card = 4} {hβ : β.card = 4}
    {b b' : Bool} {a a' : Wr 7} (ha : a ∈ memAt α hα b) (ha' : a' ∈ memAt α hα b')
    (h : mkQ 7 (a * a') = zBar β hβ) : β = α := by
  have hs : SupportedOn (a * a') (Set.range (emb α hα)) :=
    (supportedOn_of_mem_memAt ha).mul (supportedOn_of_mem_memAt ha')
  have hmemA : ∀ {c : Bool} {x : Wr 7}, x ∈ memAt α hα c → x ∈ aeSub 7 := by
    intro c x hx
    cases c
    · exact memKStar_le_aeSub _ hx
    · exact memK_le_aeSub _ hx
  have hmem : a * a' ∈ aeSub 7 := (aeSub 7).mul_mem (hmemA ha) (hmemA ha')
  have hz : zOf (emb β hβ) ∈ aeSub 7 := memK_le_aeSub _ (zOf_mem_memK _)
  rw [zBar] at h
  rcases mkQ_eq_iff.mp h with h1 | h1
  · have h1' : a * a' = zOf (emb β hβ) := inv_mul_eq_one.mp h1
    have hsub : Set.range (emb β hβ) ⊆ Set.range (emb α hα) := by
      intro x hx
      by_contra hxα
      have h2 := (hs x hxα).1
      rw [h1', zOf_vec_apply, if_pos hx] at h2
      exact one_ne_zero h2
    have h3 := range_eq_of_subset hsub
    rw [range_emb, range_emb] at h3
    exact_mod_cast h3
  · exfalso
    have h2 : zOf (emb β hβ) = (a * a') * allOnes 7 := by
      rw [← h1]
      group
    have h3 := congrArg wsum h2
    rw [wsum_mul, hmem.1, hz.1] at h3
    have h4 : wsum (allOnes 7) = 1 := by decide
    rw [h4] at h3
    exact absurd h3 (by decide)


theorem aeIdentOn_toHom' {X : Type} [Group X] {Φ : Set (Subgroup X)} {n : ℕ}
    {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AEQ n)} (hgen : pSpan Φ = ⊤)
    (I : AEIdentOn Φ n 𝒜 H) :
    ∃ f : X →* AEQ n, f.range = H ∧ f.ker ≤ Subgroup.center X ∧
      (∀ x : X, f x = I.φ ⟨x, hgen ▸ Subgroup.mem_top x⟩) ∧
      ∀ L ∈ Φ, (L.subgroupOf (pSpan Φ)).map I.φ = L.map f := by
  have hmem : ∀ x : X, x ∈ pSpan Φ := fun x => hgen ▸ Subgroup.mem_top x
  let ε : X →* ↥(pSpan Φ) :=
    { toFun := fun x => ⟨x, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hεinj : Function.Injective ε := fun x y h => congrArg Subtype.val h
  have hεsurj : Function.Surjective ε := fun z => ⟨z.1, Subtype.ext rfl⟩
  refine ⟨I.φ.comp ε, ?_, ?_, fun x => rfl, fun L hL => ?_⟩
  · refine Eq.trans ?_ I.range_eq
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ε x, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := hεsurj z
      exact ⟨x, rfl⟩
  · intro x hx
    have hx' : ε x ∈ I.φ.ker := hx
    have hc := I.ker_le hx'
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    exact hεinj (by rw [map_mul, map_mul]; exact hc (ε g))
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.1, Subgroup.mem_subgroupOf.mp hz, by
        show I.φ (ε z.1) = I.φ z
        rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ε x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem members_two_f {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ} (hn : 5 ≤ n)
    (hS : Q8Section X Φ) (f : X →* AEQ n) (hker : f.ker ≤ Subgroup.center X)
    (hlab : ∀ L ∈ Φ, ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      L.map f = memBar α h b) : ∀ L ∈ Φ, IsPGroup 2 ↥L := by
  intro L hL
  have hk : IsPGroup 2 ↥f.ker := (TL4.Vtx.isPGroup_center_of_oddFree hS.oddFree).to_le hker
  obtain ⟨α, h, b, hl⟩ := hlab L hL
  have h8 : IsPGroup 2 ↥(L.map f) := by
    rw [hl]
    exact IsPGroup.of_card (n := 3) (by rw [natCard_memBar hn]; norm_num)
  exact (h8.comap_of_ker_isPGroup f hk).to_le
    (fun x hx => Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem f hx))

theorem q8_center_sq (x : QuaternionGroup 2) (hx : ∀ y : QuaternionGroup 2, x * y = y * x) :
    x * x = 1 := by
  revert x
  decide

theorem false_of_twinFrame_aeIdentOn {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hS : Q8Section X Φ) {𝒜 : Set (Finset (Fin 7))} {H : Subgroup (AEQ 7)}
    (I : AEIdentOn Φ 7 𝒜 H) (hZ : ∀ y ∈ H, (∀ y' ∈ H, y * y' = y' * y) → y = 1)
    {A A' B : Subgroup X} {z u₁ u₂ τ ε : X} (F : TwinFrame Φ A A' B z u₁ u₂ τ ε)
    (hAA' : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) : False := by
  classical
  have hgen : pSpan Φ = ⊤ := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  obtain ⟨f, hrange, hker, hfx, hmap⟩ := aeIdentOn_toHom' hgen I
  have hlab : ∀ L ∈ Φ, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool), L.map f = memBar α h b := by
    intro L hL
    obtain ⟨α, hα, h, b, hl⟩ := I.label L hL
    exact ⟨α, hα, h, b, (hmap L hL).symm.trans hl⟩
  have h2 : ∀ L ∈ Φ, IsPGroup 2 ↥L :=
    members_two_f (by norm_num) hS f hker (fun L hL => by
      obtain ⟨α, -, h, b, hl⟩ := hlab L hL
      exact ⟨α, h, b, hl⟩)
  have h8 : ∀ L ∈ Φ, Nat.card ↥L = 8 := by
    intro L hL
    obtain ⟨e⟩ := hS.q8 L hL L (TL4.Vtx.isSylow2In_self (h2 L hL))
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hz : ∀ K ∈ Φ, ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), K.map f = memBar α h b →
      ∀ z : X, IsUniqueInvolution K z → f z = zBar α h := by
    intro K hK α hα h b hl z hzK
    have hlK : (K.subgroupOf (pSpan Φ)).map I.φ = memBar α h b := (hmap K hK).trans hl
    rw [hfx]
    exact phi_map_eq_zBar I.φ (by norm_num) hK (h8 K hK) hlK hzK
  obtain ⟨α₁, hα₁, h₁, b₁, hlA⟩ := hlab A F.hA
  obtain ⟨α₂, hα₂, h₂, b₂, hlA'⟩ := hlab A' F.hA'
  obtain ⟨β, hβ, h₃, c, hlB⟩ := hlab B F.hB
  have hzA := hz A F.hA α₁ hα₁ h₁ b₁ hlA z F.hzA
  have hzA' := hz A' F.hA' α₂ hα₂ h₂ b₂ hlA' z F.hzA'
  have hαeq : α₁ = α₂ := AE.eq_of_zBar_eq (by norm_num) (hzA.symm.trans hzA')
  subst hαeq
  have hzB := hz B F.hB β hβ h₃ c hlB τ F.htB
  have hfε : f ε = 1 := by
    have hmem : f ε ∈ H := hrange ▸ ⟨ε, rfl⟩
    refine hZ _ hmem (fun y' hy' => ?_)
    rw [← hrange] at hy'
    obtain ⟨x, rfl⟩ := hy'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp F.he x]
  obtain ⟨a₁, ha₁, ha₁e⟩ : ∃ a₁ ∈ memAt α₁ h₁ b₁, mkQ 7 a₁ = f u₁ := by
    have hm : f u₁ ∈ memBar α₁ h₁ b₁ := hlA ▸ Subgroup.mem_map_of_mem f F.h₁
    obtain ⟨a₁, ha₁, he⟩ := hm
    exact ⟨a₁, ha₁, he⟩
  obtain ⟨a₂, ha₂, ha₂e⟩ : ∃ a₂ ∈ memAt α₁ h₂ b₂, mkQ 7 a₂ = f u₂ := by
    have hm : f u₂ ∈ memBar α₁ h₂ b₂ := hlA' ▸ Subgroup.mem_map_of_mem f F.h₂
    obtain ⟨a₂, ha₂, he⟩ := hm
    exact ⟨a₂, ha₂, he⟩
  have hfτ : f τ = f u₁ * f u₂ := by
    rw [F.hrel, map_mul, map_mul, hfε, mul_one]
  have key : mkQ 7 (a₁ * a₂) = zBar β h₃ := by
    rw [map_mul, ha₁e, ha₂e, ← hfτ, hzB]
  have hβα := eq_of_mkQ_mul_eq_zBar ha₁ ha₂ key
  subst hβα
  have hfu : f (u₁ * u₂) = f z := by
    rw [map_mul, ← hfτ, hzB, hzA]
  have hκ : (u₁ * u₂)⁻¹ * z ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfu, inv_mul_cancel]
  have hκc : (u₁ * u₂)⁻¹ * z ∈ Subgroup.center X := hker hκ
  have hu₁ : ∀ a ∈ A, a * u₁ = u₁ * a := by
    intro a ha
    have hza : z * a = a * z := F.hzA.commute_of_mem ha
    have hκa : a * ((u₁ * u₂)⁻¹ * z) = ((u₁ * u₂)⁻¹ * z) * a :=
      (Subgroup.mem_center_iff.mp hκc a)
    have hu₂a : a * u₂ = u₂ * a := (hAA' a ha u₂ F.h₂)
    have hcu : a * (u₁ * u₂) = (u₁ * u₂) * a := by
      have h1 : (u₁ * u₂) = z * ((u₁ * u₂)⁻¹ * z)⁻¹ := by group
      have hcz : Commute a z := hza.symm
      have hcκ : Commute a ((u₁ * u₂)⁻¹ * z) := hκa
      rw [h1]
      exact (hcz.mul_right hcκ.inv_right).eq
    have hc2 : Commute a u₂ := hu₂a
    have hc12 : Commute a (u₁ * u₂) := hcu
    have : Commute a u₁ := by
      have := hc12.mul_right hc2.inv_right
      rwa [mul_inv_cancel_right] at this
    exact this.eq
  obtain ⟨e⟩ := hS.q8 A F.hA A (TL4.Vtx.isSylow2In_self (h2 A F.hA))
  have hsq : e ⟨u₁, F.h₁⟩ * e ⟨u₁, F.h₁⟩ = 1 := by
    refine q8_center_sq _ (fun y => ?_)
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hu₁ y' y'.2).symm
  have hu1sq : u₁ * u₁ = 1 := by
    have h1 : (⟨u₁, F.h₁⟩ : ↥A) * ⟨u₁, F.h₁⟩ = 1 := by
      apply e.injective
      rw [map_mul, hsq, map_one]
    exact congrArg Subtype.val h1
  exact F.hzA.ne_one (F.o₁ ▸ hu1sq)


theorem false_of_twinFrame_aeIdent7 {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hS : Q8Section X Φ) (I : AEIdent Φ 7)
    {A A' B : Subgroup X} {z u₁ u₂ τ ε : X} (F : TwinFrame Φ A A' B z u₁ u₂ τ ε)
    (hAA' : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) : False := by
  obtain ⟨I'⟩ := TL4.nonempty_aeIdentOn_of_aeIdent (P := Φ) (m := 7) ⟨I⟩
  exact false_of_twinFrame_aeIdentOn hS I' (aeModel_center (by norm_num)) F hAA'

theorem false_of_twinFrame_e64 {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hS : Q8Section X Φ) (I : AEIdentOn Φ 7 AE.e64Sets AE.e64Sub)
    {A A' B : Subgroup X} {z u₁ u₂ τ ε : X} (F : TwinFrame Φ A A' B z u₁ u₂ τ ε)
    (hAA' : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) : False := by
  refine false_of_twinFrame_aeIdentOn hS I (fun y hy hc => ?_) F hAA'
  have hmem : (⟨y, hy⟩ : ↥AE.e64Sub) ∈ Subgroup.center ↥AE.e64Sub := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rw [TwinDisc.E64Aut.center_e64Sub_eq_bot, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M
