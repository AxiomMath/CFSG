module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAbs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TC.Thin

@[expose] def aeMembers (k : ℕ) (𝒜 : Set (Finset (Fin k))) : Set (Subgroup (AE.AEQ k)) :=
  {M | ∃ α ∈ 𝒜, ∃ h : α.card = 4, ∃ b : Bool, M = AE.memBar α h b}

@[expose] def ModelNoS3 (k : ℕ) (𝒜 : Set (Finset (Fin k))) (H : Subgroup (AE.AEQ k)) : Prop :=
  ∀ a ∈ H, ¬ HasS3Quot ↥(Ea (aeMembers k 𝒜) a)

section Transfer

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

@[expose] def toPSpan (hgen : pSpan Φ = ⊤) : G →* ↥(pSpan Φ) :=
  MonoidHom.codRestrict (MonoidHom.id G) (pSpan Φ) (fun x => by rw [hgen]; trivial)

theorem map_toPSpan {A : Type} [Group A] (φ : ↥(pSpan Φ) →* A) (hgen : pSpan Φ = ⊤)
    {L : Subgroup G} (hL : L ∈ Φ) :
    L.map (φ.comp (toPSpan hgen)) = (L.subgroupOf (pSpan Φ)).map φ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, le_pSpan hL hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  · rintro ⟨⟨x, hxP⟩, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩

theorem psi_props (F : TwinDisc.ExitO2.Q8Fam G Φ) {k : ℕ} (hk : 5 ≤ k)
    (φ : ↥(pSpan Φ) →* AE.AEQ k) (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ))
    (hlabel : ∀ L ∈ Φ, ∃ (α : Finset (Fin k)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b) :
    (∀ L ∈ Φ, ∀ x ∈ L, (φ.comp (toPSpan F.gen)) x = 1 → x = 1) ∧
    (∀ K ∈ Φ, ∀ J ∈ Φ, K.map (φ.comp (toPSpan F.gen)) = J.map (φ.comp (toPSpan F.gen)) → K = J) ∧
    (∀ x : G, (φ.comp (toPSpan F.gen)) x = 1 → ∃ j : ℕ, x ^ (2 ^ j) = 1) := by
  set ψ := φ.comp (toPSpan F.gen) with hψ
  have hinj : ∀ L ∈ Φ, ∀ x ∈ L, ψ x = 1 → x = 1 := by
    intro L hL x hx hψx
    obtain ⟨α, h, b, hlab⟩ := hlabel L hL
    have h8 : Nat.card ↥L = 8 := (F.card L hL).trans (by norm_num)
    exact phi_injOn φ hk hL h8 hlab hx L.one_mem (by
      have : φ ⟨x, le_pSpan hL hx⟩ = 1 := hψx
      rw [this]; exact (map_one φ).symm)
  refine ⟨hinj, ?_, ?_⟩
  · intro K hK J hJ hKJ
    obtain ⟨a, haK, ha2⟩ := F.exists_mul_self_ne_one K hK
    refine TwinDisc.ExitO2.fam_eq_of_phi_mem φ F hk hker hlabel hK hJ haK ha2 ?_
    rw [← map_toPSpan φ F.gen hJ, ← hψ, ← hKJ]
    exact ⟨a, haK, rfl⟩
  · intro x hx
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : (toPSpan F.gen x : ↥(pSpan Φ)) ∈ φ.ker := hx
      have h2 := Subgroup.mem_center_iff.mp (hker h1) (toPSpan F.gen y)
      have h3 := congrArg Subtype.val h2
      exact h3
    exact center_pow_two F.oddFree hxc

theorem psi_hcent (F : TwinDisc.ExitO2.Q8Fam G Φ) {k : ℕ} (hk : 5 ≤ k)
    (φ : ↥(pSpan Φ) →* AE.AEQ k) (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ))
    (hlabel : ∀ L ∈ Φ, ∃ (α : Finset (Fin k)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b) (a : G) :
    ∀ L ∈ Φ, L.map (φ.comp (toPSpan F.gen)) ≤
        Subgroup.centralizer ({(φ.comp (toPSpan F.gen)) a} : Set (AE.AEQ k)) →
      L ≤ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨hinj, heq, -⟩ := psi_props F hk φ hker hlabel
  set ψ := φ.comp (toPSpan F.gen) with hψ
  intro L hL hc
  have hfix : ∀ x ∈ L, ψ (a * x * a⁻¹) = ψ x := by
    intro x hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hc ⟨x, hx, rfl⟩)
    rw [map_mul, map_mul, map_inv]
    calc ψ a * ψ x * (ψ a)⁻¹ = (ψ x * ψ a) * (ψ a)⁻¹ := by rw [← h1]
      _ = ψ x := mul_inv_cancel_right _ _
  have hconjmem : conjSub a L ∈ Φ := F.hyp.conjInvariant a L hL
  have himg : (conjSub a L).map ψ = L.map ψ := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hfix x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨a * x * a⁻¹, conj_mem_conjSub hx, hfix x hx⟩
  have hnorm : conjSub a L = L := heq _ hconjmem L hL himg
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxc : a * x * a⁻¹ ∈ L := by rw [← hnorm]; exact conj_mem_conjSub hx
  have h1 : a * x * a⁻¹ = x := hinj L hL _ (L.mul_mem hxc (L.inv_mem hx)) (by
    rw [map_mul, map_inv, hfix x hx, mul_inv_cancel])
    |> fun h => by
      have : a * x * a⁻¹ * x⁻¹ = 1 := h
      exact mul_inv_eq_one.mp this
  calc x * a = (a * x * a⁻¹) * a := by rw [h1]
    _ = a * x := by group

theorem image_eq_aeMembers {k : ℕ} {𝒜 : Set (Finset (Fin k))} (φ : ↥(pSpan Φ) →* AE.AEQ k)
    (hgen : pSpan Φ = ⊤)
    (hlabel : ∀ L ∈ Φ, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b) :
    (fun L => L.map (φ.comp (toPSpan hgen))) '' Φ = aeMembers k 𝒜 := by
  ext M
  constructor
  · rintro ⟨L, hL, rfl⟩
    obtain ⟨α, hα, h, b, hlab⟩ := hlabel L hL
    exact ⟨α, hα, h, b, (map_toPSpan φ hgen hL).trans hlab⟩
  · rintro ⟨α, hα, h, b, rfl⟩
    obtain ⟨L, hL, hlab⟩ := hsurj α hα h b
    exact ⟨L, hL, (map_toPSpan φ hgen hL).trans hlab⟩

theorem Ea_map_model (F : TwinDisc.ExitO2.Q8Fam G Φ) {k : ℕ} (hk : 5 ≤ k) {𝒜 : Set (Finset (Fin k))}
    (φ : ↥(pSpan Φ) →* AE.AEQ k) (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ))
    (hlabel : ∀ L ∈ Φ, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b) (a : G) :
    Ea (aeMembers k 𝒜) ((φ.comp (toPSpan F.gen)) a) = (Ea Φ a).map (φ.comp (toPSpan F.gen)) := by
  rw [← image_eq_aeMembers φ F.gen hlabel hsurj]
  exact Ea_map _ Φ a (psi_hcent F hk φ hker (fun L hL => by
    obtain ⟨α, -, h, b, hlab⟩ := hlabel L hL
    exact ⟨α, h, b, hlab⟩) a)

theorem hasS3Quot_model (F : TwinDisc.ExitO2.Q8Fam G Φ) {k : ℕ} (hk : 5 ≤ k) {𝒜 : Set (Finset (Fin k))}
    (φ : ↥(pSpan Φ) →* AE.AEQ k) (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ))
    (hlabel : ∀ L ∈ Φ, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b) {a : G} (ha : HasS3Quot ↥(Ea Φ a)) :
    HasS3Quot ↥(Ea (aeMembers k 𝒜) ((φ.comp (toPSpan F.gen)) a)) := by
  rw [Ea_map_model F hk φ hker hlabel hsurj a]
  obtain ⟨-, -, h2⟩ := psi_props F hk φ hker (fun L hL => by
    obtain ⟨α, -, h, b, hlab⟩ := hlabel L hL
    exact ⟨α, h, b, hlab⟩)
  refine HasS3Quot.of_surjective ((φ.comp (toPSpan F.gen)).subgroupMap (Ea Φ a))
    (MonoidHom.subgroupMap_surjective _ _) ?_ ha
  intro x hx
  have hx1 : (φ.comp (toPSpan F.gen)) (x : G) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    simpa using this
  obtain ⟨j, hj⟩ := h2 _ hx1
  exact ⟨j, Subtype.ext (by simpa using hj)⟩

theorem false_of_far (F : TwinDisc.ExitO2.Q8Fam G Φ) {k : ℕ} (hk : 5 ≤ k) {𝒜 : Set (Finset (Fin k))}
    (φ : ↥(pSpan Φ) →* AE.AEQ k) (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ))
    (hlabel : ∀ L ∈ Φ, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hdisj : ∀ α ∈ 𝒜, α.card = 4 → ∃ β ∈ 𝒜, ∃ (_ : β.card = 4), Disjoint α β)
    {K K' : Subgroup G} (hK : K ∈ Φ) (hne : K' ≠ K)
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K') (hK' : K' ∈ Φ) :
    False := by
  have hlabel' : ∀ L ∈ Φ, ∃ (α : Finset (Fin k)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b := fun L hL => by
    obtain ⟨α, -, h, b, hlab⟩ := hlabel L hL
    exact ⟨α, h, b, hlab⟩
  obtain ⟨-, heq, -⟩ := psi_props F hk φ hker hlabel'
  obtain ⟨α, hα, h, b, hlabK⟩ := hlabel K hK
  obtain ⟨β, hβ, hβ4, hdis⟩ := hdisj α hα h
  obtain ⟨J₁, hJ₁, hlab₁⟩ := hsurj β hβ hβ4 true
  obtain ⟨J₂, hJ₂, hlab₂⟩ := hsurj β hβ hβ4 false
  set ψ := φ.comp (toPSpan F.gen) with hψ
  have himg : ∀ J ∈ Φ, ∀ {c : Bool}, (J.subgroupOf (pSpan Φ)).map φ = AE.memBar β hβ4 c →
      J.map ψ = AE.memBar β hβ4 c := fun J hJ c hc => (map_toPSpan φ F.gen hJ).trans hc
  have hKimg : K.map ψ = AE.memBar α h b := (map_toPSpan φ F.gen hK).trans hlabK
  have hnorm : ∀ J ∈ Φ, ∀ {c : Bool}, (J.subgroupOf (pSpan Φ)).map φ = AE.memBar β hβ4 c →
      J ≤ Subgroup.normalizer (K : Set G) := by
    intro J hJ c hc x hx
    have hxJ : ψ x ∈ AE.memBar β hβ4 c := by
      rw [← himg J hJ hc]; exact ⟨x, hx, rfl⟩
    have hconj : conjSub x K ∈ Φ := F.hyp.conjInvariant x K hK
    have hcimg : (conjSub x K).map ψ = K.map ψ := by
      rw [hKimg]
      ext y
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        have ha' : ψ a ∈ AE.memBar α h b := by rw [← hKimg]; exact ⟨a, ha, rfl⟩
        have hc' := AE.comm_memBar_of_disjoint (h := h) (h' := hβ4) hdis b c (ψ a) ha' (ψ x) hxJ
        have : ψ (x * a * x⁻¹) = ψ a := by
          rw [map_mul, map_mul, map_inv]
          calc ψ x * ψ a * (ψ x)⁻¹ = (ψ a * ψ x) * (ψ x)⁻¹ := by rw [← hc']
            _ = ψ a := mul_inv_cancel_right _ _
        show ψ (x * a * x⁻¹) ∈ AE.memBar α h b
        rw [this]; exact ha'
      · intro hy
        rw [← hKimg] at hy
        obtain ⟨a, ha, rfl⟩ := hy
        have ha' : ψ a ∈ AE.memBar α h b := by rw [← hKimg]; exact ⟨a, ha, rfl⟩
        have hc' := AE.comm_memBar_of_disjoint (h := h) (h' := hβ4) hdis b c (ψ a) ha' (ψ x) hxJ
        have : ψ (x * a * x⁻¹) = ψ a := by
          rw [map_mul, map_mul, map_inv]
          calc ψ x * ψ a * (ψ x)⁻¹ = (ψ a * ψ x) * (ψ x)⁻¹ := by rw [← hc']
            _ = ψ a := mul_inv_cancel_right _ _
        exact ⟨x * a * x⁻¹, conj_mem_conjSub ha, this⟩
    have := heq _ hconj K hK (by rw [hcimg, hKimg])
    exact mem_normalizer_iff_conjSub_eq.mpr this
  have hne1 : J₁ ≠ K := fun e => AE.memBar_ne_of_disjoint (h := h) (h' := hβ4) hdis b true (by
    rw [← hKimg, ← himg J₁ hJ₁ hlab₁, e])
  have hne2 : J₂ ≠ K := fun e => AE.memBar_ne_of_disjoint (h := h) (h' := hβ4) hdis b false (by
    rw [← hKimg, ← himg J₂ hJ₂ hlab₂, e])
  have h1 := hperp J₁ hJ₁ hne1 (hnorm J₁ hJ₁ hlab₁)
  have h2 := hperp J₂ hJ₂ hne2 (hnorm J₂ hJ₂ hlab₂)
  have h12 : J₁ ≠ J₂ := fun e => AE.memBar_true_ne_false hk β hβ4 (by
    rw [← himg J₁ hJ₁ hlab₁, ← himg J₂ hJ₂ hlab₂, e])
  exact h12 (h1.trans h2.symm)

end Transfer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
